import FCAppendix.PayOnce.InactiveTruncatedFOC
import FCAppendix.PayOnce.PopulationSampling
import FCAppendix.PayOnce.CovarianceConcentration

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Filter Topology Set Game
open PayOnce PayOnce.CovarianceConcentration PayOnce.TruncatedFOC PayOnce.RareSuccessSlope PayOnce.OwnImpact
open scoped BigOperators ProbabilityTheory

theorem exists_sampled_inactive_FOC
    {m c k : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Γ : FiniteGame m (k+1) c Seed) (hk : 1 ≤ k) (hc : 0 < c) (hcm : c < m)
    (hA : Γ.A = Schedule.once (k+1)) (hG : Γ.G = Schedule.once (k+1))
    (hu : UsersOptimal Γ) (B : PosteriorSystem Γ)
    (hB : PosteriorProposerOptimalAE Γ B) (hsym : SymmetricProposersOnPath Γ)
    (hvalue : PositiveValueAtomless Γ) (hatom : PositiveVisibleAtomless Γ)
    (hinactive : InactiveAbstain Γ) :
    let P := populationLaw (ι := Fin m) (userProfileLaw Γ)
    let p := fun z : UserProfile m (k+1) × Fin m => dummyProfileMarginal Γ (by omega) z.1 z.2
    let T := fun z : UserProfile m (k+1) × Fin m => profileTruncatedValue Γ z.1 z.2
    let D := fun z : UserProfile m (k+1) × Fin m => profileEffectiveTruncatedBid Γ z.1 z.2
    ∃ weight : UserProfile m (k+1) × Fin m → ℝ,
      Measurable weight ∧ (∀ z, weight z ∈ Icc (0 : ℝ) 1) ∧
      (∫ z, T z*baseSlope (k+1) (p z) ∂P) ≤
        (∫ z, T z*weightedSlope (k+1) (p z) (weight z) ∂P)+(k+1:ℝ)^2/m ∧
      (∫ z, T z*weightedSlope (k+1) (p z) (weight z) ∂P) =
        ∫ z, D z*(success (k+1) (p z)+weightedSlope (k+1) (p z) (weight z)) ∂P := by
  have hm : 0 < m := hc.trans hcm
  letI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  let n := k+1
  have hn : 2 ≤ n := by omega
  let p := dummyProfileMarginal Γ hn
  let T := profileTruncatedValue Γ
  let D := profileEffectiveTruncatedBid Γ
  obtain ⟨weight, hw, hwb, hsum, hfirst⟩ :=
    exists_bounded_inactive_profile_FOC Γ hk hc hcm hA hG hu B hB hsym hvalue hatom hinactive
  have hp := fun i => measurable_dummyProfileMarginal Γ hn i
  have ht := measurable_profileTruncatedValue Γ
  have hd := measurable_profileEffectiveTruncatedBid Γ
  have htb d i : T d i ∈ Icc (0:ℝ) 1 := truncatedValue_bounds _
  have hdb d i : D d i ∈ Icc (0:ℝ) 1 := truncatedBid_bounds _ _
  have hf0 i : Measurable (fun d => T d i*baseSlope n (p d i)) :=
    (ht i).mul ((measurable_baseSlope n).comp (hp i))
  have hf1 i : Measurable (fun d => T d i*weightedSlope n (p d i) (weight d i)) :=
    (ht i).mul ((measurable_weightedSlope n).comp ((hp i).prodMk (hw i)))
  have hf2 i : Measurable (fun d => D d i*(success n (p d i)+weightedSlope n (p d i) (weight d i))) :=
    (hd i).mul (((continuous_success n).measurable.comp (hp i)).add
      ((measurable_weightedSlope n).comp ((hp i).prodMk (hw i))))
  have hb0 d i : ‖T d i*baseSlope n (p d i)‖ ≤ (n:ℝ)^2 := by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (htb d i).1,
      abs_of_nonneg (baseSlope_bounds hn (dummyProfileMarginal_bounds Γ hn d i)).1]
    exact (mul_le_mul_of_nonneg_right (htb d i).2
      (baseSlope_bounds hn (dummyProfileMarginal_bounds Γ hn d i)).1).trans
      (by simpa using (baseSlope_bounds hn (dummyProfileMarginal_bounds Γ hn d i)).2)
  have hb1 d i : ‖T d i*weightedSlope n (p d i) (weight d i)‖ ≤ (n:ℝ)^2 := by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (htb d i).1,
      abs_of_nonneg (weightedSlope_bounds hn (dummyProfileMarginal_bounds Γ hn d i) (hwb d i)).1]
    exact (mul_le_mul_of_nonneg_right (htb d i).2
      (weightedSlope_bounds hn (dummyProfileMarginal_bounds Γ hn d i) (hwb d i)).1).trans
      (by simpa using (weightedSlope_bounds hn (dummyProfileMarginal_bounds Γ hn d i) (hwb d i)).2)
  have hb2 d i : ‖D d i*(success n (p d i)+weightedSlope n (p d i) (weight d i))‖ ≤ 1+(n:ℝ)^2 := by
    have hs := success_mem_unit (n := n) (dummyProfileMarginal_bounds Γ hn d i)
    have hws := weightedSlope_bounds hn (dummyProfileMarginal_bounds Γ hn d i) (hwb d i)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hdb d i).1,
      abs_of_nonneg (add_nonneg hs.1 hws.1)]
    exact (mul_le_mul_of_nonneg_right (hdb d i).2 (add_nonneg hs.1 hws.1)).trans
      (by simpa using add_le_add hs.2 hws.2)
  have hi0 := integrable_populationLaw_of_bound (userProfileLaw Γ) _ hf0 hb0
  have hi1 := integrable_populationLaw_of_bound (userProfileLaw Γ) _ hf1 hb1
  have hi2 := integrable_populationLaw_of_bound (userProfileLaw Γ) _ hf2 hb2
  refine ⟨fun z => weight z.1 z.2, measurable_from_prod_countable_left hw,
    fun z => hwb z.1 z.2, ?_, ?_⟩
  · change (∫ z, T z.1 z.2*baseSlope n (p z.1 z.2) ∂populationLaw (userProfileLaw Γ)) ≤
      (∫ z, T z.1 z.2*weightedSlope n (p z.1 z.2) (weight z.1 z.2) ∂populationLaw (userProfileLaw Γ)) + (k+1:ℝ)^2/m
    rw [integral_populationLaw _ (fun d i => T d i*baseSlope n (p d i)) hi0,
      integral_populationLaw _ (fun d i => T d i*weightedSlope n (p d i) (weight d i)) hi1]
    simpa only [populationMean, Fintype.card_fin, one_mul, n, Nat.cast_add, Nat.cast_one] using
      integral_average_correction_le (userProfileLaw Γ) hn p T weight hp ht hw zero_le_one
        (fun d i => dummyProfileMarginal_bounds Γ hn d i)
        (fun d i => truncatedValue_bounds _) hwb hsum (Nat.cast_pos.mpr hm)
  · change (∫ z, T z.1 z.2*weightedSlope n (p z.1 z.2) (weight z.1 z.2) ∂populationLaw (userProfileLaw Γ)) =
      ∫ z, D z.1 z.2*(success n (p z.1 z.2)+weightedSlope n (p z.1 z.2) (weight z.1 z.2)) ∂populationLaw (userProfileLaw Γ)
    rw [integral_populationLaw _ (fun d i => T d i*weightedSlope n (p d i) (weight d i)) hi1,
      integral_populationLaw _ (fun d i => D d i*(success n (p d i)+weightedSlope n (p d i) (weight d i))) hi2]
    rw [integral_populationMean _ _ (fun i => Integrable.of_bound (hf1 i).aestronglyMeasurable _
      (Eventually.of_forall fun d => hb1 d i)),
      integral_populationMean _ _ (fun i => Integrable.of_bound (hf2 i).aestronglyMeasurable _
      (Eventually.of_forall fun d => hb2 d i))]
    exact congrArg populationMean (funext hfirst)

end FCAppendix.Bayes
