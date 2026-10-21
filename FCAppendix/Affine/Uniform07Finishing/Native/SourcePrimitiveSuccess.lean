import FCAppendix.Affine.Uniform07Finishing.Native.SourceSuccessRates
import FCAppendix.Affine.Uniform07Finishing.Native.SourceUpperImbalance
import FCAppendix.Affine.Uniform07Finishing.Native.AuxiliaryProducerData

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing
open MeasureTheory ProbabilityTheory Game Bayes Set Filter Topology Classical
open StrictNative ConditionalSuccess
variable {m : ℕ} [Nonempty (Fin m)]

theorem literalSource_bad_mass_from_five_scalar_rates (row : Uniform07.Row)
    (hm : 2 ≤ m) (hc : 1 ≤ Uniform07.capacity m)
    {R Λ z width ε C γ : ℝ} (hR : 0 < R) (hUR : Early.bidCap row < R)
    (hRt : R < Uniform07.cutoff row) (hε : 0 < ε)
    (hΛ : (54/100 : ℝ)*Uniform07.cutoff row < Λ)
    (hz : (52/100 : ℝ)*Uniform07.cutoff row < z)
    (PL : ProbabilityMeasure (ℝ × JointAction 2))
    (hLvalue : (PL : Measure (ℝ × JointAction 2)).map Prod.fst =
      (sourceLowerValueLaw row : Measure ℝ))
    (hLroute : ∀ᵐ x ∂(PL : Measure (ℝ × JointAction 2)),
      x.2.bid ≤ Early.bidCap row ∧ x.2.routeCount = 2)
    (hLbidValue : ∀ᵐ x ∂(PL : Measure (ℝ × JointAction 2)), x.2.bid ≤ x.1)
    (hLatom : ∀ b : ℝ, (PL : Measure (ℝ × JointAction 2)) {x | x.2.bid = b} = 0)
    (hguard : ∀ i (A : JointAction 2), A.bid < R → ∀ τ j k,
      (userProfileLaw (literalSourceNativeGame row hc R Λ z width ε hΛ PL)).real
        (sourceScalarGuardFailure row R Λ z width ε i A τ j k) ≤ C*Real.exp (-γ*(m : ℝ))) :
    ∀ i (A : JointAction 2), A.bid < R →
      (userProfileLaw (literalSourceNativeGame row hc R Λ z width ε hΛ PL)).real
        (sourceSuccessGood row hc R Λ z width ε PL i A)ᶜ ≤
          sourceSuccessProbabilityError row ε C γ 10 m := by
  apply literalSource_bad_mass_from_scalar_rates row hm hc hR hUR hRt hε hΛ hz
    (by norm_num : (0 : ℝ)≤ 10) PL hLvalue hLroute hLbidValue hLatom hguard
  intro i A _ τ j
  exact literalSource_deviation_upper_second_le row hm hc hR hUR hRt hΛ PL
    hLvalue hLroute i A τ j

namespace UniformAuxiliaryData05

theorem eventually_success_good_mass_rate (D : UniformAuxiliaryData05) (row : Uniform07.Row) :
    ∀ᶠ k in atTop, ∀ i : Fin (D.start+k), ∀ A : JointAction 2,
      A.bid<(D.market row k).R →
      (userProfileLaw (D.market row k).native).real
        (@sourceSuccessGood (D.start+k) (D.market row k).fin_nonempty row (D.market row k).capacity_positive
          (D.market row k).R (D.market row k).Λ (D.market row k).z
          (D.market row k).width (D.market row k).guardMargin (D.market row k).lower i A)ᶜ ≤
        sourceSuccessProbabilityError row (D.fixed_guard_margin row)
          (D.guard_constant row) (D.guard_rate row) 10 (D.start+k) := by
  filter_upwards [D.scalar_concentration row] with k hk
  let M := D.market row k
  letI : Nonempty (Fin (D.start+k)) := M.fin_nonempty
  have hh := literalSource_bad_mass_from_five_scalar_rates row M.market_ge_two M.capacity_positive
    M.floor_positive M.cap_lt_floor M.floor_lt_cutoff M.guard_margin_positive
    M.multiplier_lower (D.rejection_root row k) M.lower M.lower_value M.lower_routes
    (D.lower_no_overbid row k) M.lower_atomless hk
  have he : sourceSuccessProbabilityError row M.guardMargin
      (D.guard_constant row) (D.guard_rate row) 10 (D.start+k) =
      sourceSuccessProbabilityError row (D.fixed_guard_margin row)
        (D.guard_constant row) (D.guard_rate row) 10 (D.start+k) := by
    dsimp only [M]
    rw [D.guard_margin_eq row k]
  intro i A hA
  have hh' := hh i A hA
  rw [he] at hh'
  convert! hh' using 1

theorem eventually_success_good_mass_small (D : UniformAuxiliaryData05) (row : Uniform07.Row) :
    ∀ᶠ k in atTop, ∀ i : Fin (D.start+k), ∀ A : JointAction 2,
      A.bid<(D.market row k).R →
      (userProfileLaw (D.market row k).native).real
        (@sourceSuccessGood (D.start+k) (D.market row k).fin_nonempty row (D.market row k).capacity_positive
          (D.market row k).R (D.market row k).Λ (D.market row k).z
          (D.market row k).width (D.market row k).guardMargin (D.market row k).lower i A)ᶜ ≤
          (1-sourceLowerMarginalCap row)^2/2 := by
  have he := D.population_tendsto.eventually
    (eventually_sourceSuccessProbabilityError_small row (C := D.guard_constant row)
      (D.fixed_guard_margin_positive row) (D.guard_rate_positive row) (by norm_num : (0 : ℝ)≤ 10))
  filter_upwards [D.eventually_success_good_mass_rate row,he] with k hk he
  intro i A hA
  exact (hk i A hA).trans he

theorem eventually_all_success_good_mass_small (D : UniformAuxiliaryData05) :
    ∀ᶠ k in atTop, ∀ row : Uniform07.Row, ∀ i : Fin (D.start+k), ∀ A : JointAction 2,
      A.bid<(D.market row k).R →
      (userProfileLaw (D.market row k).native).real
        (@sourceSuccessGood (D.start+k) (D.market row k).fin_nonempty row (D.market row k).capacity_positive
          (D.market row k).R (D.market row k).Λ (D.market row k).z
          (D.market row k).width (D.market row k).guardMargin (D.market row k).lower i A)ᶜ ≤
          (1-sourceLowerMarginalCap row)^2/2 := by
  filter_upwards [D.eventually_success_good_mass_small .first,
    D.eventually_success_good_mass_small .second] with k h₁ h₂
  intro row
  cases row
  · exact h₁
  · exact h₂

theorem eventually_all_lower_action_success_cap (D : UniformAuxiliaryData05) :
    ∀ᶠ k in atTop, ∀ row : Uniform07.Row, ∀ i : Fin (D.start+k), ∀ A : JointAction 2,
      A.bid<(D.market row k).R →
      ((problem (D.market row k).native i).outcome A).success ≤ sourceLowerSuccessCap row := by
  filter_upwards [D.eventually_all_success_good_mass_small] with k hk
  intro row
  let M := D.market row k
  letI : Nonempty (Fin (D.start+k)) := M.fin_nonempty
  apply sourceNative_lower_success_cap_of_plan_bad_mass row (by have := M.market_ge_two; omega)
    M.capacity_positive M.floor_positive (le_of_eq (D.auxiliary_floor row k))
    M.multiplier_lower M.guard_margin_positive M.lower
  exact hk row

end UniformAuxiliaryData05
end FCAppendix.Affine.Uniform07Finishing
