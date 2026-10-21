import FCAppendix.Affine.Uniform07Finishing.Native.SourceDeficitMoment
import FCAppendix.Affine.Uniform07Finishing.Native.SourceSuccessBadEvents

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing
open MeasureTheory ProbabilityTheory Game Bayes Set Filter Topology Classical
open StrictNative ConditionalSuccess
open scoped BigOperators
variable {m : ℕ} [Nonempty (Fin m)]

lemma source_seed_erasure_guards (row : Uniform07.Row) {Λ z : ℝ}
    (hΛ : (54/100 : ℝ)*Uniform07.cutoff row < Λ)
    (hz : (52/100 : ℝ)*Uniform07.cutoff row < z) :
    0 ≤ Uniform07.cutoff row/2 ∧
      Uniform07.cutoff row/2 ≤ Λ-Early.nativeRadius row ∧
      Uniform07.cutoff row/2 ≤ z ∧ Uniform07.cutoff row/2 ≤ Early.bidCap row := by
  have ht := Uniform07.cutoff_pos row
  have hh := (le_max_right _ _).trans_lt ((Early.native_sampling_margin_guards row).2 Λ hΛ).1
  exact ⟨by positivity,by linarith,by linarith,(source_seed_cutoff_lt_bidCap row).le⟩

theorem sourceExclusiveHit_le_sqrt_moment (row : Uniform07.Row)
    (hm : 0 < m) (hc : 1 ≤ Uniform07.capacity m)
    {R Λ z width ε : ℝ} (hUR : Early.bidCap row < R) (hε : 0 < ε)
    (hΛ : (54/100 : ℝ)*Uniform07.cutoff row < Λ)
    (hz : (52/100 : ℝ)*Uniform07.cutoff row < z)
    (PL : ProbabilityMeasure (ℝ × JointAction 2))
    (μ : Measure (UserDraw 2)) [IsProbabilityMeasure μ]
    (hseedLaw : sourceSeedMeasure row m hc R PL =
      (cond μ (sourceDrawTag (Uniform07.cutoff row/2) (Early.bidCap row) ⁻¹' {0})).map
        (fun u : UserDraw 2 => u.1.2.bid))
    (hroute : ∀ᵐ u ∂μ, u.1.2.bid ≤ Uniform07.cutoff row/2 → u.1.2.routeCount = 2)
    (hnoatoms : ∀ b : ℝ,
      ((cond μ (sourceDrawTag (Uniform07.cutoff row/2) (Early.bidCap row) ⁻¹' {0})).map
        (fun u : UserDraw 2 => u.1.2.bid)) {b} = 0)
    (i : Fin m) (A : JointAction 2) (hA : A.bid < R)
    (τ : Equiv.Perm (Fin 2)) (j : Fin 2) (M : ℝ) (hM : 0 ≤ M)
    (hsecond : (∫ d, ((observedContext R j (deviationList i A d τ j)).2.1-
      (observedContext R j (deviationList i A d τ j)).2.2 : ℝ)^2
        ∂Measure.pi (fun _ : Fin m => μ)) ≤ M) :
    (Measure.pi (fun _ : Fin m => μ)).real
      (sourceExclusiveHit row hc R Λ z width ε PL i A τ j) ≤ Real.sqrt M/(ε*m) := by
  by_cases hs : A.bid ≤ Uniform07.cutoff row/2
  · rw [sourceExclusiveHit_empty_of_ineligible row hc R Λ z width ε hΛ PL i A hA
      (Or.inl hs) τ j]
    simpa only [Measure.real,measure_empty,ENNReal.toReal_zero] using
      div_nonneg (Real.sqrt_nonneg M) (mul_nonneg hε.le (Nat.cast_nonneg m))
  · have hseed := source_seed_erasure_guards row hΛ hz
    have hzR := (source_seed_cutoff_lt_bidCap row).trans hUR
    let ν := Measure.pi (fun _ : Fin m => μ)
    let P := fun d : UserProfile m 2 => sourceSuccessPlan row hc R Λ z width ε PL
      (observedContext R j (deviationList i A d τ j))
    have hP : Measurable P := (measurable_sourceSuccessPlan row hc R Λ z width ε hΛ PL).comp
      ((measurable_observedContext R j).comp (measurable_deviationList_profile i A τ j))
    have hE := measurableSet_sourceExclusiveHit row hc R Λ z width ε hΛ PL i A τ j
    have hindicator : ν.real (sourceExclusiveHit row hc R Λ z width ε PL i A τ j) ≤
        ∫ d, Weighted.planTargetIndicator i (P d) ∂ν := by
      rw [←integral_indicator_one hE]
      apply integral_mono ((integrable_const (1 : ℝ)).indicator hE)
        (integrable_planTargetIndicator ν i P hP)
      intro d
      by_cases hd : d ∈ sourceExclusiveHit row hc R Λ z width ε PL i A τ j
      · rw [Set.indicator_of_mem hd]
        rcases hd with ⟨_,E,hE',hi⟩
        change 1 ≤ Weighted.planTargetIndicator i (P d)
        simp only [P,hE',Weighted.planTargetIndicator,
          FCAppendix.Affine.WeightedSampling.indicator,if_pos hi,le_refl]
      · rw [Set.indicator_of_notMem hd]
        exact (planTargetIndicator_bounds i (P d)).1
    have htarget := source_target_integral_full_le (t := Uniform07.cutoff row) (width := width) μ i hm hε (Uniform07.xi_pos row)
      (Early.native_sampling_margin_guards row).1 (source_guard_root_positive row hΛ)
      (div_pos (Uniform07.cutoff_pos row) (by norm_num : (0 : ℝ) < 1000))
      hseed.1 hzR (Early.demandRatio_pos row) hseed.2.1 hseed.2.2.1 hseed.2.2.2
      (Uniform07.capacity m) A (lt_of_not_ge hs) τ j hroute hnoatoms
    have ht : (∫ d, Weighted.planTargetIndicator i (P d) ∂ν) ≤
        (∫ d, sourceContextDeficit (Uniform07.capacity m)
          (observedContext R j (deviationList i A d τ j)) ∂ν)/(ε*m) := by
      simpa only [P,sourceSuccessPlan,literalSourceAlpha,hseedLaw] using htarget
    exact (hindicator.trans ht).trans
      (div_le_div_of_nonneg_right
        (source_deviation_deficit_integral_le_sqrt μ (Uniform07.capacity m) R i A τ j M hM hsecond)
        (mul_nonneg hε.le (Nat.cast_nonneg m)))

def sourceSuccessProbabilityError (row : Uniform07.Row) (ε C γ V : ℝ) (m : ℕ) : ℝ :=
  4*(5*(C*Real.exp (-γ*(m : ℝ)))+
    Real.exp (-((m-1 : ℕ) : ℝ)*(Uniform07.cutoff row/2))+
    Real.sqrt (V*(m : ℝ))/(ε*(m : ℝ)))

theorem sourceSuccessProbabilityError_nonneg (row : Uniform07.Row)
    {ε C γ V : ℝ} (hε : 0 < ε) (hC : 0 ≤ C) (m : ℕ) :
    0 ≤ sourceSuccessProbabilityError row ε C γ V m := by
  unfold sourceSuccessProbabilityError
  positivity

theorem sourceSuccessProbabilityError_tendsto_zero (row : Uniform07.Row)
    {ε C γ V : ℝ} (hε : 0 < ε) (hγ : 0 < γ) (hV : 0 ≤ V) :
    Tendsto (sourceSuccessProbabilityError row ε C γ V) atTop (𝓝 0) := by
  have hN : Tendsto (fun m : ℕ => (m : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have he : Tendsto (fun m : ℕ => Real.exp (-γ*(m : ℝ))) atTop (𝓝 0) := by
    convert Real.tendsto_exp_neg_atTop_nhds_zero.comp (hN.const_mul_atTop hγ) using 1
    funext m
    congr 1
    ring
  have hs : Tendsto (fun m : ℕ => Real.exp (-((m-1 : ℕ) : ℝ)*(Uniform07.cutoff row/2)))
      atTop (𝓝 0) := by
    have hN' := hN.comp (tendsto_sub_atTop_nat 1)
    convert Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (hN'.const_mul_atTop (half_pos (Uniform07.cutoff_pos row))) using 1
    funext m
    congr 1
    simp only [Function.comp_apply]
    ring
  have hr : Tendsto (fun m : ℕ => Real.sqrt (V*(m : ℝ))/(ε*(m : ℝ)))
      atTop (𝓝 0) := by
    have hh : Tendsto (fun m : ℕ => (Real.sqrt V/ε)/Real.sqrt (m : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp hN)
    apply hh.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with m hm
    have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
    have hmS : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr hmR
    rw [Real.sqrt_mul hV]
    have heq := Real.sq_sqrt hmR.le
    field_simp [hε.ne',hmR.ne',hmS.ne']
    nlinarith [congrArg (fun x : ℝ => Real.sqrt V*x) heq]
  unfold sourceSuccessProbabilityError
  have hall := (((he.const_mul C).const_mul 5).add hs).add hr
  simpa only [mul_zero,add_zero] using hall.const_mul 4

theorem eventually_sourceSuccessProbabilityError_small (row : Uniform07.Row)
    {ε C γ V : ℝ} (hε : 0 < ε) (hγ : 0 < γ) (hV : 0 ≤ V) :
    ∀ᶠ m in atTop, sourceSuccessProbabilityError row ε C γ V m ≤
      (1-sourceLowerMarginalCap row)^2/2 := by
  have hgap : 0 < (1-sourceLowerMarginalCap row)^2/2 :=
    half_pos (sq_pos_of_pos (sub_pos.mpr (sourceLowerMarginalCap_bounds row).2))
  exact ((sourceSuccessProbabilityError_tendsto_zero row hε hγ hV).eventually
    (Iio_mem_nhds hgap)).mono (fun _ h => h.le)

theorem literalSource_bad_mass_from_scalar_rates (row : Uniform07.Row)
    (hm : 2 ≤ m) (hc : 1 ≤ Uniform07.capacity m)
    {R Λ z width ε C γ V : ℝ} (hR : 0 < R) (hUR : Early.bidCap row < R)
    (hRt : R < Uniform07.cutoff row) (hε : 0 < ε)
    (hΛ : (54/100 : ℝ)*Uniform07.cutoff row < Λ)
    (hz : (52/100 : ℝ)*Uniform07.cutoff row < z) (hV : 0 ≤ V)
    (PL : ProbabilityMeasure (ℝ × JointAction 2))
    (hLvalue : (PL : Measure (ℝ × JointAction 2)).map Prod.fst =
      (sourceLowerValueLaw row : Measure ℝ))
    (hLroute : ∀ᵐ x ∂(PL : Measure (ℝ × JointAction 2)),
      x.2.bid ≤ Early.bidCap row ∧ x.2.routeCount = 2)
    (hLbidValue : ∀ᵐ x ∂(PL : Measure (ℝ × JointAction 2)), x.2.bid ≤ x.1)
    (hLatom : ∀ b : ℝ, (PL : Measure (ℝ × JointAction 2)) {x | x.2.bid = b} = 0)
    (hguard : ∀ i (A : JointAction 2), A.bid < R → ∀ τ j k,
      (userProfileLaw (literalSourceNativeGame row hc R Λ z width ε hΛ PL)).real
        (sourceScalarGuardFailure row R Λ z width ε i A τ j k) ≤ C*Real.exp (-γ*(m : ℝ)))
    (hsecond : ∀ i (A : JointAction 2), A.bid < R → ∀ τ j,
      (∫ d, ((observedContext R j (deviationList i A d τ j)).2.1-
        (observedContext R j (deviationList i A d τ j)).2.2 : ℝ)^2
        ∂userProfileLaw (literalSourceNativeGame row hc R Λ z width ε hΛ PL)) ≤ V*(m : ℝ)) :
    ∀ i (A : JointAction 2), A.bid < R →
      (userProfileLaw (literalSourceNativeGame row hc R Λ z width ε hΛ PL)).real
        (sourceSuccessGood row hc R Λ z width ε PL i A)ᶜ ≤
          sourceSuccessProbabilityError row ε C γ V m := by
  let α := literalSourceAlpha (m := m) row Λ z width ε
  have hα : Measurable α := measurable_literalSourceAlpha row hΛ z width ε
  let Γ := sourceNativeGame row hc R Λ (source_guard_multiplier_positive row hΛ) PL α hα
  have hjoint : ∀ᵐ x ∂Γ.F⊗ₘΓ.σ,
      (x.2.bid ≤ Early.bidCap row ∧ x.2.routeCount = 2) ∨
        (R ≤ x.2.bid ∧ x.2.routeCount = 1) := by
    rw [sourceNativeGame_joint_law row hm hc hR hRt
      (source_guard_multiplier_positive row hΛ) PL hLvalue hLroute α hα]
    filter_upwards [source_population_support row m hm hc hR hRt PL hLvalue hLroute] with x hx
    rcases hx with hl | hu
    · exact Or.inl hl.2.2
    · exact Or.inr ⟨hu.2.2.2.1,hu.2.2.2.2.2⟩
  have hdraw : ∀ᵐ u ∂userLaw Γ,
      (u.1.2.bid ≤ Early.bidCap row ∧ u.1.2.routeCount = 2) ∨
        (R ≤ u.1.2.bid ∧ u.1.2.routeCount = 1) :=
    (measurePreserving_fst (μ := Γ.F⊗ₘΓ.σ) (ν := permLaw 2)).quasiMeasurePreserving.ae hjoint
  have hroute : ∀ᵐ u ∂userLaw Γ,
      u.1.2.bid ≤ Uniform07.cutoff row/2 → u.1.2.routeCount = 2 := by
    filter_upwards [hdraw] with u hu
    intro hb
    rcases hu with hl | hh
    · exact hl.2
    · exact ((not_lt_of_ge hh.1) (hb.trans_lt ((source_seed_cutoff_lt_bidCap row).trans hUR))).elim
  have hshape : ∀ᵐ d ∂userProfileLaw Γ, ∀ i,
      SourceRivalShape (Early.bidCap row) R i d := by
    have hfull : ∀ᵐ d ∂userProfileLaw Γ, ∀ u,
        ((d u).1.2.bid ≤ Early.bidCap row ∧ (d u).1.2.routeCount = 2) ∨
          (R ≤ (d u).1.2.bid ∧ (d u).1.2.routeCount = 1) :=
      ae_all_iff.mpr (fun u =>
        (measurePreserving_eval (fun _ : Fin m => userLaw Γ) u).quasiMeasurePreserving.ae hdraw)
    exact hfull.mono (fun d hd i u _ => hd u)
  letI : NullSingletonClass (submittedBidMeasure Γ) := by
    unfold submittedBidMeasure
    rw [sourceNativeGame_joint_law row hm hc hR hRt
      (source_guard_multiplier_positive row hΛ) PL hLvalue hLroute α hα]
    exact source_population_bid_atomless row m hm hc hR hRt PL hLatom
  have hnoatoms := actual_conditional_bid_atomless Γ
    ((measurable_sourceDrawTag (Uniform07.cutoff row/2) (Early.bidCap row))
      (measurableSet_singleton (0 : Fin 3)))
  have hseedLaw : sourceSeedMeasure row m hc R PL =
      (cond (userLaw Γ)
        (sourceDrawTag (Uniform07.cutoff row/2) (Early.bidCap row) ⁻¹' {0})).map
        (fun u : UserDraw 2 => u.1.2.bid) := by
    rw [sourceDrawTag_seed]
    exact sourceNativeGame_seed_measure row hm hc hR hRt
      (source_guard_multiplier_positive row hΛ) PL hLvalue hLroute α hα
  have hseed := sourceNativeGame_seed_real_lower row hm hc hR hRt
    (source_guard_multiplier_positive row hΛ) PL hLvalue hLroute hLbidValue α hα
  intro i A hA
  apply sourceSuccess_bad_mass_le row (by omega) hc hUR hε PL (userProfileLaw Γ) i A
    (hshape.mono (fun _ hd => hd i)) (hguard i A hA)
  · intro τ j
    exact source_focal_seed_failure_le_exp row hc hUR PL (userLaw Γ) i A
      (hshape.mono (fun _ hd => hd i)) hseed τ j
  · intro τ j
    exact sourceExclusiveHit_le_sqrt_moment row (by omega) hc hUR hε hΛ hz PL
      (userLaw Γ) hseedLaw hroute hnoatoms i A hA τ j (V*(m : ℝ))
      (mul_nonneg hV (Nat.cast_nonneg m)) (hsecond i A hA τ j)

end FCAppendix.Affine.Uniform07Finishing
