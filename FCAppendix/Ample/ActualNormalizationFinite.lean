import FCAppendix.Ample.CommonRateActualAdapters
import FCAppendix.Game.JointMeasurability
import FCAppendix.Finite.BalancedOrder

noncomputable section
namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology
open scoped ENNReal BigOperators
open Ample Ample.DownstreamNormalizationCore

variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem activeSurplusLaw_probability (F : Measure ℝ) [IsFiniteMeasure F]
    (g : ℝ) (hactive : F (Ioi g) ≠ 0) :
    IsProbabilityMeasure (activeSurplusLaw F g) := by
  let ν : Measure ℝ := (F (Ioi g))⁻¹ • F.restrict (Ioi g)
  letI : IsProbabilityMeasure ν := ⟨by
    change ((F (Ioi g))⁻¹ • F.restrict (Ioi g)) univ = 1
    rw [Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ]
    simp only [univ_inter, smul_eq_mul]
    exact ENNReal.inv_mul_cancel hactive (measure_ne_top F _)⟩
  exact ν.isProbabilityMeasure_map (measurable_id.sub_const g).aemeasurable

theorem activeSurplusLaw_finite (F : Measure ℝ) [IsFiniteMeasure F] (g : ℝ) :
    IsFiniteMeasure (activeSurplusLaw F g) := by
  by_cases hz : F (Ioi g) = 0
  · have hr : F.restrict (Ioi g) = 0 := Measure.restrict_eq_zero.mpr hz
    rw [activeSurplusLaw, hr, smul_zero, Measure.map_zero]
    infer_instance
  · letI := activeSurplusLaw_probability F g hz
    infer_instance

theorem exists_activeEndpoint (F : Measure ℝ) [IsProbabilityMeasure F]
    (g : ℝ) (hactive : 0 < F.real (Ioi g)) :
    ∃ ell : ℝ, IsActiveEndpoint F g ell := by
  classical
  have hactive' : F (Ioi g) ≠ 0 := by
    intro hz
    simp [Measure.real, hz] at hactive
  let ν := activeSurplusLaw F g
  letI : IsProbabilityMeasure ν := activeSurplusLaw_probability F g hactive'
  have hzero : ν (Iic 0) = 0 := activeSurplusLaw_nonpositive_null F g
  let S : Set ℝ := {a | 0 < ν (Iic a)}
  have hne : S.Nonempty := by
    by_contra hn
    have hnull (a : ℝ) : ν (Iic a) = 0 := by
      apply le_antisymm _ bot_le
      exact le_of_not_gt (fun ha => hn ⟨a, ha⟩)
    have hcover : (⋃ k : ℕ, Iic (k : ℝ)) = (univ : Set ℝ) := by
      ext x
      simp only [mem_iUnion, mem_Iic, mem_univ, iff_true]
      obtain ⟨k, hk⟩ := exists_nat_gt x
      exact ⟨k, hk.le⟩
    have hnullU : ν univ = 0 := by
      rw [← hcover]
      exact measure_iUnion_null (fun k => hnull (k : ℝ))
    simp at hnullU
  have hlo : ∀ a ∈ S, 0 ≤ a := by
    intro a ha
    by_contra hn
    have ha0 : a < 0 := lt_of_not_ge hn
    have hz : ν (Iic a) = 0 :=
      measure_mono_null (fun x hx => hx.trans ha0.le) hzero
    exact (ne_of_gt ha) hz
  have hbelow : BddBelow S := ⟨0, hlo⟩
  let ell : ℝ := sInf S
  have hell : 0 ≤ ell := le_csInf hne hlo
  refine ⟨ell, hell, ?_, ?_⟩
  · have hcover : Iio ell = ⋃ k : ℕ, Iic (ell - 1 / ((k : ℝ) + 1)) := by
      ext x
      simp only [mem_Iio, mem_iUnion, mem_Iic]
      constructor
      · intro hx
        have hlim : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
          tendsto_one_div_add_atTop_nhds_zero_nat
        obtain ⟨k, hk⟩ := (hlim.eventually_lt_const (sub_pos.mpr hx)).exists
        exact ⟨k, by linarith⟩
      · rintro ⟨k, hk⟩
        have hpos : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
        linarith
    change ν (Iio ell) = 0
    rw [hcover]
    apply measure_iUnion_null
    intro k
    by_contra hn
    have hs : ell - 1 / ((k : ℝ) + 1) ∈ S := pos_iff_ne_zero.mpr hn
    have hle : ell ≤ ell - 1 / ((k : ℝ) + 1) := csInf_le hbelow hs
    have hpos : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    linarith
  · intro a ha
    obtain ⟨b, hb, hba⟩ := exists_lt_of_csInf_lt hne ha
    exact hb.trans_le (measure_mono (fun x hx => hx.trans hba.le))

theorem activeDrawLaw_ae_of_restrict (Γ : FiniteGame m n c Seed)
    {P : ℝ × JointAction n → Prop}
    (h : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ).restrict {x | Γ.g < x.1}, P x) :
    ∀ᵐ x ∂activeDrawLaw Γ, P x := by
  rw [ae_iff] at h ⊢
  simp only [activeDrawLaw, Measure.smul_apply, smul_eq_mul, h, mul_zero]

theorem activeDrawLaw_ae_of_joint (Γ : FiniteGame m n c Seed)
    {P : ℝ × JointAction n → Prop}
    (h : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), P x) :
    ∀ᵐ x ∂activeDrawLaw Γ, P x :=
  activeDrawLaw_ae_of_restrict Γ (ae_restrict_of_ae h)

theorem activeDrawLaw_active (Γ : FiniteGame m n c Seed) :
    ∀ᵐ x ∂activeDrawLaw Γ, Γ.g < x.1 :=
  activeDrawLaw_ae_of_restrict Γ
    (ae_restrict_mem (measurableSet_lt measurable_const measurable_fst))

theorem activeDrawLaw_bestReply (Γ : FiniteGame m n c Seed) (hm : 0 < m)
    (hA : Γ.A = Schedule.ppi n) (hf : FreeDuplicateBase Γ)
    (hu : UsersOptimal Γ) :
    ∀ᵐ x ∂activeDrawLaw Γ,
      0 ≤ x.1 - Γ.g ∧ IsBestReply (actualMenu Γ) (x.1 - Γ.g) x.2 := by
  filter_upwards [activeDrawLaw_active Γ,
    activeDrawLaw_ae_of_joint Γ (ae_bestResponse_compProd Γ hu ⟨0, hm⟩)] with x hx hbr
  refine ⟨(sub_pos.mpr hx).le, ?_⟩
  exact actualMenu_bestReply Γ hm hA hf (by simpa only [sub_add_cancel] using hbr)

theorem outcome_load_le_routeCount (Γ : FiniteGame m n c Seed) (i : Fin m)
    (a : JointAction n) : ((problem Γ i).outcome a).load ≤ a.routeCount := by
  calc
    _ ≤ (a.routeCount : ℝ) * ((problem Γ i).outcome a).success :=
      load_le_routeCount_mul_success Γ i a
    _ ≤ (a.routeCount : ℝ) * 1 :=
      mul_le_mul_of_nonneg_left ((problem Γ i).outcome a).success_le_one
        (Nat.cast_nonneg _)
    _ = _ := mul_one _

theorem outcome_copy_error_zero_of_route_zero (Γ : FiniteGame m n c Seed)
    (i : Fin m) (a : JointAction n) (hk : a.routeCount = 0) :
    ((problem Γ i).outcome a).prob (fun r => r.val ≠ a.routeCount) = 0 := by
  classical
  have hz (ω : Sample m n Seed) : (focalCount Γ i a ω).val = 0 := by
    have hh := focalCount_le Γ i a ω
    rw [hk] at hh
    exact Nat.eq_zero_of_le_zero hh
  rw [FiniteLaw.prob_eq_expect, problem_outcome, CountLaw.expect_ofMeasure]
  simp only [hk, hz, ne_eq, not_true_eq_false, if_false, integral_zero]

theorem actualMenu_semantics (Γ : FiniteGame m n c Seed) (hm : 0 < m) :
    (∀ a, a.routeCount = 0 → actualFailure Γ a = 1) ∧
    (∀ a, 0 ≤ (a.routeCount : ℝ) ∧ 0 ≤ a.bid ∧
      0 ≤ actualMeanLoad Γ a ∧ actualMeanLoad Γ a ≤ a.routeCount ∧
      (actualMenu Γ).payment a = a.bid * actualMeanLoad Γ a) := by
  constructor
  · intro a hk
    have hL := outcome_load_le_routeCount Γ ⟨0, hm⟩ a
    rw [hk, Nat.cast_zero] at hL
    have hS : ((problem Γ ⟨0, hm⟩).outcome a).success = 0 :=
      le_antisymm (((problem Γ ⟨0, hm⟩).outcome a).success_le_load.trans hL)
        ((problem Γ ⟨0, hm⟩).outcome a).success_nonneg
    simp only [actualFailure, dif_pos hm, hS, sub_zero]
  · intro a
    refine ⟨Nat.cast_nonneg _, a.bid_nonneg, ?_, ?_, rfl⟩
    · simpa only [actualMeanLoad, dif_pos hm] using
        ((problem Γ ⟨0, hm⟩).outcome a).load_nonneg
    · simpa only [actualMeanLoad, dif_pos hm] using
        outcome_load_le_routeCount Γ ⟨0, hm⟩ a

theorem outcome_acceptance_error_le_copy_error (Γ : FiniteGame m n c Seed)
    (i : Fin m) (a : JointAction n) (hk : 0 < a.routeCount) :
    |((problem Γ i).outcome a).load / (a.routeCount : ℝ) - 1| ≤
      ((problem Γ i).outcome a).prob (fun r => r.val ≠ a.routeCount) := by
  classical
  let μ := (problem Γ i).outcome a
  have hkR : (0 : ℝ) < a.routeCount := Nat.cast_pos.mpr hk
  have hlow : (a.routeCount : ℝ) * μ.prob (fun r => r.val = a.routeCount) ≤ μ.load := by
    rw [FiniteLaw.prob_eq_expect, ← FiniteLaw.expect_const_mul]
    apply μ.expect_mono
    intro r
    by_cases hr : r.val = a.routeCount
    · simp only [hr, if_true, mul_one, le_refl]
    · simp only [hr, if_false, mul_zero]
      exact Nat.cast_nonneg _
  have hp := μ.prob_compl (fun r => r.val = a.routeCount)
  have hu : μ.load / (a.routeCount : ℝ) ≤ 1 :=
    (div_le_one hkR).mpr (outcome_load_le_routeCount Γ i a)
  have hl : μ.prob (fun r => r.val = a.routeCount) ≤ μ.load / (a.routeCount : ℝ) :=
    (le_div_iff₀ hkR).mpr (by simpa only [mul_comm] using hlow)
  rw [abs_of_nonpos (sub_nonpos.mpr hu)]
  change μ.prob (fun r => r.val ≠ a.routeCount) =
    1 - μ.prob (fun r => r.val = a.routeCount) at hp
  linarith

theorem actual_acceptance_error_le_copy_error (Γ : FiniteGame m n c Seed)
    (hm : 0 < m) (a : JointAction n) (hk : 0 < a.routeCount) :
    |actualMeanLoad Γ a / (a.routeCount : ℝ) - 1| ≤
      ((problem Γ ⟨0, hm⟩).outcome a).prob (fun r => r.val ≠ a.routeCount) := by
  simpa only [actualMeanLoad, dif_pos hm] using
    outcome_acceptance_error_le_copy_error Γ ⟨0, hm⟩ a hk

theorem actualFailure_measurable (Γ : FiniteGame m n c Seed) :
    Measurable (actualFailure Γ) := by
  unfold actualFailure
  by_cases hm : 0 < m
  · simp only [dif_pos hm]
    exact measurable_const.sub (measurable_success Γ ⟨0, hm⟩)
  · simpa only [dif_neg hm] using
      (measurable_const : Measurable (fun _ : JointAction n => (1 : ℝ)))

theorem actualDeficit_measurable (Γ : FiniteGame m n c Seed) :
    Measurable (actualDeficit Γ) := by
  unfold actualDeficit
  by_cases hm : 0 < m
  · simp only [dif_pos hm, deficit]
    have henv := (problem Γ ⟨0, hm⟩).envelope_lipschitzWith.continuous.measurable
    exact
      measurable_id.sub (henv.comp (measurable_id.add_const (problem Γ ⟨0, hm⟩).g))
  · simp only [dif_neg hm]
    exact measurable_id

theorem actualMeanLoad_measurable (Γ : FiniteGame m n c Seed) :
    Measurable (actualMeanLoad Γ) := by
  unfold actualMeanLoad
  by_cases hm : 0 < m
  · simp only [dif_pos hm, CountLaw.load]
    exact
      measurable_outcome_expect Γ ⟨0, hm⟩ (fun r => (r.val : ℝ))
  · simpa only [dif_neg hm] using
      (measurable_const : Measurable (fun _ : JointAction n => (0 : ℝ)))

theorem actual_normalized_deficit_measurable (Γ : FiniteGame m n c Seed) (g z : ℝ) :
    Measurable (fun x : ℝ × JointAction n =>
      actualDeficit Γ (x.1-g) / actualDeficit Γ z - 1) :=
  (((actualDeficit_measurable Γ).comp (measurable_fst.sub_const g)).div_const
    (actualDeficit Γ z)).sub_const 1

theorem actual_normalized_failure_measurable (Γ : FiniteGame m n c Seed) (z : ℝ) :
    Measurable (fun x : ℝ × JointAction n => actualFailure Γ x.2 / actualDeficit Γ z) :=
  ((actualFailure_measurable Γ).comp measurable_snd).div_const (actualDeficit Γ z)

theorem actual_normalized_bid_measurable (Γ : FiniteGame m n c Seed) (z : ℝ) :
    Measurable (fun x : ℝ × JointAction n =>
      (x.2.routeCount : ℝ) * x.2.bid / actualDeficit Γ z - 1) := by
  have hk : Measurable (fun x : ℝ × JointAction n => (x.2.routeCount : ℝ)) :=
    (measurable_of_countable (fun k : ℕ => (k : ℝ))).comp
      ((measurable_routeCount n).comp measurable_snd)
  exact ((hk.mul ((measurable_bid n).comp measurable_snd)).div_const
    (actualDeficit Γ z)).sub_const 1

theorem active_uniform_acceptance_of_joint_copy_error
    {M C : ℕ → ℕ} (Γ : ∀ t, FiniteGame (M t) n (C t) Seed)
    (hM : ∀ᶠ t in atTop, 0 < M t) (e : ℕ → ℝ)
    (he : Tendsto e atTop (𝓝 0))
    (hcopy : ∀ᶠ t in atTop, ∀ i : Fin (M t), ∀ᵐ x ∂((Γ t).F ⊗ₘ (Γ t).σ),
      ((problem (Γ t) i).outcome x.2).prob (fun r => r.val ≠ x.2.routeCount) ≤ e t) :
    ∀ eps > 0, ∀ᶠ t in atTop, ∀ᵐ x ∂activeDrawLaw (Γ t),
      0 < x.2.routeCount →
        |actualMeanLoad (Γ t) x.2 / (x.2.routeCount : ℝ) - 1| ≤ eps := by
  intro eps heps
  filter_upwards [hM, hcopy, he.eventually_lt_const heps] with t ht hc he'
  filter_upwards [activeDrawLaw_ae_of_joint (Γ t) (hc ⟨0, ht⟩)] with x hx
  intro hk
  exact (actual_acceptance_error_le_copy_error (Γ t) ht x.2 hk).trans
    (hx.trans he'.le)

end FCAppendix.Bayes
