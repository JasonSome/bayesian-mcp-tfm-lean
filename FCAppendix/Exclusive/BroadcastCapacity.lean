import FCAppendix.Exclusive.SampledAggregates
import FCAppendix.PayOnce.ActiveProfileMeans

namespace FCAppendix.Bayes

open MeasureTheory ProbabilityTheory Game Set Filter Topology
open PayOnce.CovarianceConcentration
open scoped BigOperators ProbabilityTheory

variable {m n c k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

def ExclusiveBroadcastOn (Γ : FiniteGame m n c Seed) (E : Set ℝ) : Prop :=
  ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ),
    (x.1 ∈ E → 0 < x.2.bid ∧ x.2.routeCount = n) ∧
    (x.1 ∉ E → x.2.routeCount = 0)

theorem ExclusiveBroadcastOn.routes {Γ : FiniteGame m n c Seed} {E : Set ℝ}
    (h : ExclusiveBroadcastOn Γ E) :
    ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), x.2.routeCount = 0 ∨ (0 < x.2.bid ∧ x.2.routeCount = n) := by
  filter_upwards [h] with x hx
  by_cases he : x.1 ∈ E
  · exact Or.inr (hx.1 he)
  · exact Or.inl (hx.2 he)

noncomputable def typeEventCount (E : Set ℝ) (d : UserProfile m n) : ℕ :=
  Probability.sampleCount {u : UserDraw n | u.1.1 ∈ E} d

theorem measurable_typeEventCount (E : Set ℝ) (hE : MeasurableSet E) :
    Measurable (typeEventCount (m := m) (n := n) E) :=
  Probability.measurable_sampleCount _ (hE.preimage (measurable_fst.comp measurable_fst)) m

theorem ae_visibleCard_eq_typeEventCount (Γ : FiniteGame m n c Seed)
    (E : Set ℝ) (hclass : ExclusiveBroadcastOn Γ E) (j : Fin n) :
    ∀ᵐ d ∂userProfileLaw Γ,
      Fintype.card (VisibleUser (observe (drawsRealization d) j)) = typeEventCount E d := by
  classical
  have hdraw := ae_all_iff.mpr fun i =>
    (profileAction_measurePreserving Γ i).quasiMeasurePreserving.ae hclass
  filter_upwards [hdraw] with d hd
  let ℓ := observe (drawsRealization d) j
  have he (i : Fin m) : ℓ i ≠ none ↔ (d i).1.1 ∈ E := by
    by_cases hv : (d i).1.1 ∈ E
    · have hr := (hd i).1 hv
      have hentry : ℓ i = some (d i).1.2.bid := by
        simp [ℓ, observe, drawsRealization, mem_firstK, hr.2]
      simp [hentry, hv]
    · have hr := (hd i).2 hv
      simp [ℓ, observe, drawsRealization, mem_firstK, hr, hv]
  let e : VisibleUser ℓ ≃ {i : Fin m // (d i).1.1 ∈ E} :=
    { toFun := fun i => ⟨i.val, (he i.val).mp i.property⟩
      invFun := fun i => ⟨i.val, (he i.val).mpr i.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  calc
    _ = Fintype.card {i : Fin m // (d i).1.1 ∈ E} := Fintype.card_congr e
    _ = typeEventCount E d := by simp [typeEventCount, Probability.sampleCount, Fintype.card_subtype]

theorem ae_exclusive_profileLoad_eq_typeCapacity (Γ : FiniteGame m (k + 1) c Seed)
    (hk : 1 ≤ k) (B : PosteriorSystem Γ) (hB : ExclusiveOptimalOnPath Γ B)
    (hsym : SymmetricProposersOnPath Γ) (E : Set ℝ) (hclass : ExclusiveBroadcastOn Γ E) :
    ∀ᵐ d ∂userProfileLaw Γ, profileLoad Γ d =
      ((k + 1 : ℕ) : ℝ) * (min c (typeEventCount E d) : ℕ) / m := by
  let j : Fin (k + 1) := ⟨0, by omega⟩
  filter_upwards [ae_exclusive_profile_laws Γ hk B hB hsym hclass.routes j,
    ae_visibleCard_eq_typeEventCount Γ E hclass j] with d hd hcard
  unfold profileLoad
  simp_rw [hd.1, IndependentCounts.binomial_load]
  rw [← Finset.mul_sum, hd.2.1, hcard]

theorem exclusive_type_fraction_L1
    {M C : ℕ → ℕ} (Γ : ∀ t, FiniteGame (M t) n (C t) Seed)
    (hM : Tendsto M atTop atTop) (E : Set ℝ) (hE : MeasurableSet E)
    (h : ℝ) (hmass : ∀ t, (Γ t).F.real E = h) :
    Tendsto (fun t => ∫ d, |(typeEventCount E d : ℝ) / M t - h|
      ∂userProfileLaw (Γ t)) atTop (𝓝 0) := by
  classical
  let f : ℝ → ℝ := E.indicator (fun _ => 1)
  have hf : Measurable f := measurable_const.indicator hE
  have hb (v : ℝ) : f v ∈ Icc (0 : ℝ) 1 := by
    by_cases hv : v ∈ E <;> simp [f, hv]
  have hrate : Tendsto (fun t => (1 : ℝ) / Real.sqrt (M t)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, one_div] using tendsto_inv_atTop_zero.comp
      (Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp hM))
  apply squeeze_zero' (Eventually.of_forall fun _ => integral_nonneg fun _ => abs_nonneg _) _ hrate
  filter_upwards [hM.eventually_gt_atTop 0] with t ht
  have hh := integral_profileMeanType_error_le (Γ t) ht f hf hb
  have he : (∫ v, f v ∂(Γ t).F) = h := (integral_indicator_one hE).trans (hmass t)
  rw [he] at hh
  simpa [f, profileMeanType, typeEventCount, Probability.sampleCount, indicator_apply] using hh

theorem integrable_typeEventFraction (Γ : FiniteGame m n c Seed)
    (E : Set ℝ) (hE : MeasurableSet E) :
    Integrable (fun d => (typeEventCount E d : ℝ) / m) (userProfileLaw Γ) := by
  classical
  apply UnitInterval.integrable
  · exact ((measurable_of_countable (fun q : ℕ => (q : ℝ))).comp
      (measurable_typeEventCount (m := m) (n := n) E hE)).div_const m
  · intro d
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · intro d
    by_cases hm : m = 0
    · simp [hm]
    · have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm)
      apply (div_le_one hmR).mpr
      have hc : typeEventCount E d ≤ m := by
        unfold typeEventCount Probability.sampleCount
        exact (Finset.card_filter_le _ _).trans_eq (by simp)
      exact_mod_cast hc

theorem exclusive_broadcast_load_limit
    {M C : ℕ → ℕ} (Γ : ∀ t, FiniteGame (M t) (k + 1) (C t) Seed)
    (hk : 1 ≤ k) (hM : Tendsto M atTop atTop)
    (B : ∀ t, PosteriorSystem (Γ t)) (hB : ∀ t, ExclusiveOptimalOnPath (Γ t) (B t))
    (hsym : ∀ t, SymmetricProposersOnPath (Γ t))
    (E : Set ℝ) (hE : MeasurableSet E) (hclass : ∀ t, ExclusiveBroadcastOn (Γ t) E)
    {h rho : ℝ} (hmass : ∀ t, (Γ t).F.real E = h)
    (hrho : Tendsto (fun t => (C t : ℝ) / M t) atTop (𝓝 rho)) (hcap : rho ≤ h) :
    Tendsto (fun t => finiteLoad (Γ t)) atTop (𝓝 (((k + 1 : ℕ) : ℝ) * rho)) := by
  let a := fun t (d : UserProfile (M t) (k + 1)) => (typeEventCount E d : ℝ) / M t
  have ha t : Integrable (a t) (userProfileLaw (Γ t)) := integrable_typeEventFraction (Γ t) E hE
  have hfrac := exclusive_type_fraction_L1 Γ hM E hE h hmass
  have hclip := integral_min_mean_tendsto (fun t => userProfileLaw (Γ t)) a ha
    (fun t => (C t : ℝ) / M t) hcap hrho hfrac
  have hmean : Tendsto (fun t => ∫ d, min ((C t : ℝ) / M t) (a t d)
      ∂userProfileLaw (Γ t)) atTop (𝓝 rho) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simp only [Real.norm_eq_abs]
    apply squeeze_zero (fun _ => abs_nonneg _) _ hclip
    intro t
    have hi : Integrable (fun d => min ((C t : ℝ) / M t) (a t d))
        (userProfileLaw (Γ t)) := (integrable_const ((C t : ℝ) / M t)).inf (ha t)
    have he : (∫ d, min ((C t : ℝ) / M t) (a t d) ∂userProfileLaw (Γ t)) - rho =
        ∫ d, min ((C t : ℝ) / M t) (a t d) - rho ∂userProfileLaw (Γ t) := by
      rw [integral_sub hi (integrable_const rho)]
      simp
    rw [he]
    simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
      (fun d => min ((C t : ℝ) / M t) (a t d) - rho)
  have hmul := hmean.const_mul (((k + 1 : ℕ) : ℝ))
  apply hmul.congr'
  filter_upwards [hM.eventually_gt_atTop 0] with t _ht
  rw [← integral_const_mul]
  change (∫ d, _ ∂userProfileLaw (Γ t)) = finiteLoad (Γ t)
  apply integral_congr_ae
  filter_upwards [ae_exclusive_profileLoad_eq_typeCapacity (Γ t) hk (B t) (hB t)
    (hsym t) E (hclass t)] with d hd
  rw [hd, Nat.cast_min]
  dsimp only [a]
  rw [min_div_div_right (Nat.cast_nonneg (M t))]
  ring

end FCAppendix.Bayes
