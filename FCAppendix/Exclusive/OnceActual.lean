import FCAppendix.Exclusive.OnceRouting
import FCAppendix.Probability.UniformCoordinate

namespace FCAppendix.Bayes

open MeasureTheory ProbabilityTheory Game Filter
open scoped ProbabilityTheory BigOperators

variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem exclusive_ae_routed_bid_pos_userLaw (Γ : FiniteGame m n c Seed)
    (hv : VisibleAtomless Γ) :
    ∀ᵐ d ∂userLaw Γ, 0 < d.1.2.routeCount → 0 < d.1.2.bid := by
  classical
  have hall : ∀ᵐ d ∂userLaw Γ, ∀ j : Fin n,
      ¬ (j ∈ firstK d.2 d.1.2.routeCount ∧ d.1.2.bid = 0) :=
    ae_all_iff.mpr fun j => measure_eq_zero_iff_ae_notMem.mp (hv j 0)
  filter_upwards [hall] with d hd hk
  have hcard : 0 < (firstK d.2 d.1.2.routeCount).card := by
    rwa [card_firstK _ _ d.1.2.routeCount_le]
  obtain ⟨j, hj⟩ := Finset.card_pos.mp hcard
  exact lt_of_le_of_ne d.1.2.bid_nonneg (fun h => hd j ⟨hj, h.symm⟩)

theorem exclusive_ae_routed_bid_pos (Γ : FiniteGame m n c Seed)
    (hv : VisibleAtomless Γ) :
    ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), 0 < x.2.routeCount → 0 < x.2.bid := by
  have h := Measure.ae_ae_of_ae_prod (exclusive_ae_routed_bid_pos_userLaw Γ hv)
  filter_upwards [h] with x hx
  exact hx.exists.choose_spec

theorem exclusive_ae_zero_or_full_routes (Γ : FiniteGame m n c Seed)
    (hv : VisibleAtomless Γ)
    (hr : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), 0 < x.2.bid → 0 < x.2.routeCount → x.2.routeCount = n) :
    ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), x.2.routeCount = 0 ∨ x.2.routeCount = n := by
  filter_upwards [exclusive_ae_routed_bid_pos Γ hv, hr] with x hp hx
  by_cases hk : x.2.routeCount = 0
  · exact Or.inl hk
  · exact Or.inr (hx (hp (Nat.pos_of_ne_zero hk)) (Nat.pos_of_ne_zero hk))

theorem exclusive_ae_inactive_count_zero (Γ : FiniteGame m n c Seed)
    (hu : UsersOptimal Γ) (hv : VisibleAtomless Γ) (i : Fin m) :
    ∀ᵐ ω ∂backgroundLaw Γ, (ω.1 i).1.1 ≤ Γ.g → playedCount Γ i ω = 0 := by
  have hd := (measurePreserving_eval (fun _ : Fin m => userLaw Γ) i).quasiMeasurePreserving.ae
    (exclusive_ae_routed_bid_pos_userLaw Γ hv)
  have hb := (measurePreserving_fst (μ := userProfileLaw Γ)
    (ν := Measure.pi fun _ : Fin n => Γ.seedLaw)).quasiMeasurePreserving.ae hd
  filter_upwards [hb, ae_played_overbid_zero Γ hu i] with ω hbid hzero hw
  by_cases hk : (ω.1 i).1.2.routeCount = 0
  · apply Fin.ext
    exact abstention_count_zero (drawsRealization ω.1) Γ.policy ω.2 i hk
  · apply hzero
    have hpos := hbid (Nat.pos_of_ne_zero hk)
    change max ((ω.1 i).1.1 - Γ.g) 0 < (ω.1 i).1.2.bid
    simpa only [max_eq_right (sub_nonpos.mpr hw)] using hpos

noncomputable def exclusiveMarginal (Γ : FiniteGame m n c Seed) (j : Fin n)
    (d : UserProfile m n) (i : Fin m) : ℝ :=
  Proposer.marginal (seedLottery Γ j (observe (drawsRealization d) j)) i

theorem exclusiveMarginal_bounds (Γ : FiniteGame m n c Seed) (j : Fin n)
    (d : UserProfile m n) (i : Fin m) :
    0 ≤ exclusiveMarginal Γ j d i ∧ exclusiveMarginal Γ j d i ≤ 1 :=
  ⟨CommonList.marginal_nonneg _ _, CommonList.marginal_le_one _ _⟩

theorem exclusiveMarginal_eq_integral (Γ : FiniteGame m n c Seed) (j : Fin n)
    (d : UserProfile m n) (i : Fin m) :
    exclusiveMarginal Γ j d i = ∫ s, (if i ∈
      (Γ.policy j (observe (drawsRealization d) j) s).val then (1 : ℝ) else 0) ∂Γ.seedLaw := by
  classical
  rw [exclusiveMarginal, Proposer.marginal, FiniteLaw.prob_eq_expect, seedLottery,
    FiniteLaw.expect_ofMeasure]

theorem measurable_exclusiveMarginal (Γ : FiniteGame m n c Seed)
    (j : Fin n) (i : Fin m) : Measurable (fun d => exclusiveMarginal Γ j d i) := by
  classical
  simp_rw [exclusiveMarginal_eq_integral]
  have hm : Measurable (fun z : UserProfile m n × Seed =>
      if i ∈ (Γ.policy j (observe (drawsRealization z.1) j) z.2).val then (1 : ℝ) else 0) :=
    (measurable_of_countable (fun S : Finset (Fin m) => if i ∈ S then (1 : ℝ) else 0)).comp
      ((Γ.policy_measurable j).comp
        (((measurable_observe_draws j).comp measurable_fst).prodMk measurable_snd))
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

theorem exclusiveMarginal_capacity (Γ : FiniteGame m n c Seed)
    (j : Fin n) (d : UserProfile m n) :
    (∑ i, exclusiveMarginal Γ j d i) ≤ (c : ℝ) :=
  Proposer.marginal_capacity _ c (seedLottery_feasible Γ j _)

theorem exclusive_ae_inactive_marginal_zero (Γ : FiniteGame m n c Seed)
    (hu : UsersOptimal Γ) (hv : VisibleAtomless Γ) (j : Fin n) :
    ∀ᵐ d ∂userProfileLaw Γ, ∀ i, (d i).1.1 ≤ Γ.g → exclusiveMarginal Γ j d i = 0 := by
  classical
  apply ae_all_iff.mpr
  intro i
  have hh := Measure.ae_ae_of_ae_prod (exclusive_ae_inactive_count_zero Γ hu hv i)
  filter_upwards [hh] with d hd hw
  let f : Seed → ℝ := fun s =>
    if i ∈ (Γ.policy j (observe (drawsRealization d) j) s).val then 1 else 0
  have hf : Measurable f := (measurable_of_countable
    (fun S : Finset (Fin m) => if i ∈ S then (1 : ℝ) else 0)).comp
      (measurable_policy_at_list Γ j _)
  have he : ∀ᵐ s ∂(Measure.pi fun _ : Fin n => Γ.seedLaw), f (s j) = 0 := by
    filter_upwards [hd] with s hs
    have hn := notMem_allocation_of_playedCount_zero Γ i (d, s) (hs hw) j
    change i ∉ (Γ.policy j (observe (drawsRealization d) j) (s j)).val at hn
    exact if_neg hn
  have hmap := measurePreserving_eval (fun _ : Fin n => Γ.seedLaw) j
  have he' : ∀ᵐ s ∂Γ.seedLaw, f s = 0 := by
    rw [← hmap.map_eq]
    exact (ae_map_iff hmap.measurable.aemeasurable
      (measurableSet_eq_fun hf measurable_const)).mpr he
  rw [exclusiveMarginal_eq_integral]
  exact integral_eq_zero_of_ae he'

theorem exclusive_ae_profile_binomial (Γ : FiniteGame m n c Seed)
    (hr : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), x.2.routeCount = 0 ∨ x.2.routeCount = n)
    (hsym : SymmetricProposersOnPath Γ) (j : Fin n) :
    ∀ᵐ d ∂userProfileLaw Γ, ∀ i, profileCountLaw Γ d i =
      IndependentCounts.binomial n (exclusiveMarginal Γ j d i)
        (exclusiveMarginal_bounds Γ j d i).1 (exclusiveMarginal_bounds Γ j d i).2 := by
  have hsymd := ae_of_ae_map (measurable_observe_draws j).aemeasurable (hsym j)
  filter_upwards [ae_commonLists_of_zero_or_full_routes Γ hr j, hsymd] with d hd hs i
  exact profileCountLaw_binomial Γ d _ hd _ hs i

noncomputable def exclusivePosteriorPlayedCountLaw (Γ : FiniteGame m n c Seed)
    (B : PosteriorSystem Γ) (j : Fin n) (ℓ : LocalList m) (i : Fin m) : CountLaw n :=
  CountLaw.ofMeasure (posteriorBackground Γ B j ℓ) (playedCount Γ i)
    (measurable_playedCount Γ i)

theorem exclusivePosteriorPlayedCountLaw_binomial (Γ : FiniteGame m n c Seed)
    (B : PosteriorSystem Γ) (j : Fin n) (ℓ : LocalList m)
    (hcommon : ∀ᵐ d ∂B.posterior j ℓ, ∀ l, observe (drawsRealization d) l = ℓ)
    (μ : FiniteLaw (Finset (Fin m))) (hμ : SymmetricAtList Γ ℓ μ) (i : Fin m) :
    exclusivePosteriorPlayedCountLaw Γ B j ℓ i =
      IndependentCounts.binomial n (Proposer.marginal μ i)
        (CommonList.marginal_nonneg μ i) (CommonList.marginal_le_one μ i) := by
  let T : Background m n Seed → (Fin n → Seed) := Prod.snd
  have hT : MeasurePreserving T (posteriorBackground Γ B j ℓ)
      (Measure.pi fun _ : Fin n => Γ.seedLaw) :=
    measurePreserving_snd (μ := B.posterior j ℓ)
      (ν := Measure.pi fun _ : Fin n => Γ.seedLaw)
  have hfirst : ∀ᵐ ω ∂posteriorBackground Γ B j ℓ,
      ∀ l, observe (drawsRealization ω.1) l = ℓ :=
    (measurePreserving_fst (μ := B.posterior j ℓ)
      (ν := Measure.pi fun _ : Fin n => Γ.seedLaw)).quasiMeasurePreserving.ae hcommon
  have he : playedCount Γ i =ᵐ[posteriorBackground Γ B j ℓ]
      commonSeedCount Γ ℓ i ∘ T := by
    filter_upwards [hfirst] with ω hω
    exact boundedCount_eq_commonSeedCount Γ ω.1 ℓ hω i ω.2
  have hbase : exclusivePosteriorPlayedCountLaw Γ B j ℓ i =
      FiniteLaw.ofMeasure (posteriorBackground Γ B j ℓ) (playedCount Γ i)
        (measurable_playedCount Γ i) := by
    apply FiniteLaw.ext_expect
    intro f
    rw [exclusivePosteriorPlayedCountLaw, CountLaw.expect_ofMeasure, FiniteLaw.expect_ofMeasure]
  rw [hbase, FiniteLaw.ofMeasure_congr_ae _ _ _ _ ((measurable_commonSeedCount Γ ℓ i).comp
    hT.measurable) he, FiniteLaw.ofMeasure_comp_measurePreserving _ _ T hT]
  exact commonSeedCount_binomial Γ ℓ μ hμ i

noncomputable def exclusivePopulationLaw (Γ : FiniteGame m n c Seed) :
    Measure (UserProfile m n × Fin m) :=
  (userProfileLaw Γ).prod (uniformOn Set.univ)

instance exclusivePopulationLaw_isProbability (Γ : FiniteGame m n c Seed) [NeZero m] :
    IsProbabilityMeasure (exclusivePopulationLaw Γ) := by
  unfold exclusivePopulationLaw
  infer_instance

noncomputable def exclusivePopulationMarginal (Γ : FiniteGame m n c Seed) (j : Fin n)
    (z : UserProfile m n × Fin m) : ℝ := exclusiveMarginal Γ j z.1 z.2

theorem measurable_exclusivePopulationMarginal (Γ : FiniteGame m n c Seed) (j : Fin n) :
    Measurable (exclusivePopulationMarginal Γ j) :=
  measurable_from_prod_countable_left (measurable_exclusiveMarginal Γ j)

def exclusiveActiveEvent (Γ : FiniteGame m n c Seed) : Set (UserProfile m n × Fin m) :=
  {z | Γ.g < (z.1 z.2).1.1}

noncomputable def exclusiveActiveMass (Γ : FiniteGame m n c Seed) : ℝ :=
  Γ.F.real (Set.Ioi Γ.g)

theorem measurableSet_exclusiveActiveEvent (Γ : FiniteGame m n c Seed) :
    MeasurableSet (exclusiveActiveEvent Γ) :=
  measurableSet_lt measurable_const (measurable_from_prod_countable_left fun i =>
    measurable_fst.comp (measurable_fst.comp (measurable_pi_apply i)))

theorem exclusivePopulationMarginal_capacity (Γ : FiniteGame m n c Seed)
    (hm : 0 < m) (j : Fin n) :
    (∫ z, exclusivePopulationMarginal Γ j z ∂exclusivePopulationLaw Γ) ≤ (c : ℝ) / m := by
  unfold exclusivePopulationMarginal
  rw [exclusivePopulationLaw,
    Probability.integral_prod_uniform_fin (userProfileLaw Γ)
      (exclusiveMarginal Γ j) (measurable_exclusiveMarginal Γ j) 1
      (fun d i => by rw [Real.norm_eq_abs, abs_of_nonneg (exclusiveMarginal_bounds Γ j d i).1]
                     exact (exclusiveMarginal_bounds Γ j d i).2)]
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hi : Integrable (fun d => (∑ i, exclusiveMarginal Γ j d i) / (m : ℝ))
      (userProfileLaw Γ) := by
    exact (integrable_finsetSum _ (fun i _ =>
      UnitInterval.integrable _ _ (measurable_exclusiveMarginal Γ j i)
        (fun d => (exclusiveMarginal_bounds Γ j d i).1)
        (fun d => (exclusiveMarginal_bounds Γ j d i).2))).div_const (m : ℝ)
  have h := integral_mono hi (integrable_const ((c : ℝ) / m))
    (fun d => div_le_div_of_nonneg_right (exclusiveMarginal_capacity Γ j d) hmR.le)
  simpa using h

theorem exclusiveActiveEvent_mass (Γ : FiniteGame m n c Seed) (hm : 0 < m) :
    (exclusivePopulationLaw Γ).real (exclusiveActiveEvent Γ) = exclusiveActiveMass Γ := by
  classical
  let f : UserProfile m n → Fin m → ℝ := fun d i => if Γ.g < (d i).1.1 then 1 else 0
  have hf (i : Fin m) : Measurable (fun d => f d i) :=
    Measurable.ite (measurableSet_lt measurable_const
      (measurable_fst.comp (measurable_fst.comp (measurable_pi_apply i))))
      measurable_const measurable_const
  have hb (d : UserProfile m n) (i : Fin m) : ‖f d i‖ ≤ 1 := by dsimp [f]; split <;> norm_num
  have hvalue (i : Fin m) : MeasurePreserving (fun d : UserProfile m n => (d i).1.1)
      (userProfileLaw Γ) Γ.F :=
    (show MeasurePreserving (Prod.fst : ℝ × JointAction n → ℝ) (Γ.F ⊗ₘ Γ.σ) Γ.F from
      ⟨measurable_fst, Measure.fst_compProd Γ.F Γ.σ⟩).comp
      ((measurePreserving_fst (μ := Γ.F ⊗ₘ Γ.σ) (ν := permLaw n)).comp
        (measurePreserving_eval (fun _ : Fin m => userLaw Γ) i))
  have he (i : Fin m) : (∫ d, f d i ∂userProfileLaw Γ) = exclusiveActiveMass Γ := by
    have hh : Measurable (fun v : ℝ => if Γ.g < v then (1 : ℝ) else 0) :=
      Measurable.ite measurableSet_Ioi measurable_const measurable_const
    calc
      _ = ∫ v, (if Γ.g < v then (1 : ℝ) else 0) ∂Γ.F := by
        rw [← (hvalue i).map_eq]
        exact (integral_map (hvalue i).measurable.aemeasurable hh.aestronglyMeasurable).symm
      _ = _ := by
        simpa only [exclusiveActiveMass, Set.indicator, Set.mem_Ioi, Pi.one_apply] using
          (integral_indicator_one (μ := Γ.F) measurableSet_Ioi)
  calc
    _ = ∫ z, f z.1 z.2 ∂exclusivePopulationLaw Γ := by
      symm
      simpa only [f, exclusiveActiveEvent, Set.indicator, Set.mem_setOf_eq, Pi.one_apply] using
        (integral_indicator_one (μ := exclusivePopulationLaw Γ) (measurableSet_exclusiveActiveEvent Γ))
    _ = ∫ d, (∑ i, f d i) / m ∂userProfileLaw Γ :=
      Probability.integral_prod_uniform_fin (userProfileLaw Γ) f hf 1 hb
    _ = _ := by
      rw [integral_div, integral_finsetSum _ (fun i _ =>
        Integrable.of_bound (hf i).aestronglyMeasurable 1 (Eventually.of_forall fun d => hb d i))]
      simp only [he, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      exact mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr hm.ne')

theorem exclusivePopulationMarginal_supported (Γ : FiniteGame m n c Seed)
    (hm : 0 < m) (hu : UsersOptimal Γ) (hv : VisibleAtomless Γ) (j : Fin n) :
    ∀ᵐ z ∂exclusivePopulationLaw Γ, z ∉ exclusiveActiveEvent Γ →
      exclusivePopulationMarginal Γ j z = 0 := by
  letI : NeZero m := ⟨hm.ne'⟩
  have hd := (measurePreserving_fst (μ := userProfileLaw Γ)
    (ν := uniformOn (Set.univ : Set (Fin m)))).quasiMeasurePreserving.ae
      (exclusive_ae_inactive_marginal_zero Γ hu hv j)
  filter_upwards [hd] with z hz hnot
  exact hz z.2 (le_of_not_gt hnot)

theorem exclusive_actual_moment_identities (Γ : FiniteGame m n c Seed)
    (hr : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), x.2.routeCount = 0 ∨ x.2.routeCount = n)
    (hsym : SymmetricProposersOnPath Γ) (j : Fin n) :
    finiteCoverage Γ = ∫ z, PayOnce.success n (exclusivePopulationMarginal Γ j z)
      ∂exclusivePopulationLaw Γ ∧
    finiteLoad Γ = (n : ℝ) * ∫ z, exclusivePopulationMarginal Γ j z ∂exclusivePopulationLaw Γ := by
  have hl := exclusive_ae_profile_binomial Γ hr hsym j
  have hp (i : Fin m) := measurable_exclusiveMarginal Γ j i
  have hsucc (i : Fin m) : Measurable (fun d => PayOnce.success n (exclusiveMarginal Γ j d i)) :=
    (PayOnce.continuous_success n).measurable.comp (hp i)
  have hsbound (d : UserProfile m n) (i : Fin m) :
      ‖PayOnce.success n (exclusiveMarginal Γ j d i)‖ ≤ 1 := by
    have h0 : 0 ≤ PayOnce.success n (exclusiveMarginal Γ j d i) := by
      have h := CountLaw.success_nonneg (IndependentCounts.binomial n _
        (exclusiveMarginal_bounds Γ j d i).1 (exclusiveMarginal_bounds Γ j d i).2)
      simpa only [IndependentCounts.binomial_success, PayOnce.success] using h
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    exact PayOnce.success_le_one n _ (exclusiveMarginal_bounds Γ j d i).2
  have hpbound (d : UserProfile m n) (i : Fin m) : ‖exclusiveMarginal Γ j d i‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (exclusiveMarginal_bounds Γ j d i).1]
    exact (exclusiveMarginal_bounds Γ j d i).2
  constructor
  · unfold exclusivePopulationMarginal
    rw [exclusivePopulationLaw,
      Probability.integral_prod_uniform_fin (userProfileLaw Γ) _ hsucc 1 hsbound]
    apply integral_congr_ae
    filter_upwards [hl] with d hd
    unfold profileCoverage
    simp_rw [hd, IndependentCounts.binomial_success, PayOnce.success]
  · unfold exclusivePopulationMarginal
    rw [exclusivePopulationLaw,
      Probability.integral_prod_uniform_fin (userProfileLaw Γ) _ hp 1 hpbound,
      ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hl] with d hd
    unfold profileLoad
    simp_rw [hd, IndependentCounts.binomial_load]
    rw [← Finset.mul_sum, mul_div_assoc]

theorem exclusive_nat_duplicate_cast (k : ℕ) :
    ((k - 1 : ℕ) : ℝ) = (k : ℝ) - successIndicator k := by
  cases k with
  | zero => simp [successIndicator]
  | succ k => simp [successIndicator, Nat.cast_add, Nat.cast_one]

noncomputable def finiteExclusiveDuplicates (Γ : FiniteGame m n c Seed) : ℝ :=
  (∑ i, ∫ ω, (((playedCount Γ i ω).val - 1 : ℕ) : ℝ) ∂backgroundLaw Γ) / m

theorem finiteExclusiveDuplicates_eq_load_sub_coverage (Γ : FiniteGame m n c Seed) :
    finiteExclusiveDuplicates Γ = finiteLoad Γ - finiteCoverage Γ := by
  classical
  rw [finiteExclusiveDuplicates, finiteLoad_eq_actual, finiteCoverage_eq_actual,
    ← sub_div, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp_rw [exclusive_nat_duplicate_cast]
  exact integral_sub
    (CountLaw.integrable_comp (backgroundLaw Γ) _ (measurable_playedCount Γ i)
      (fun r => (r.val : ℝ)))
    (CountLaw.integrable_comp (backgroundLaw Γ) _ (measurable_playedCount Γ i)
      (fun r => successIndicator r.val))

end FCAppendix.Bayes
