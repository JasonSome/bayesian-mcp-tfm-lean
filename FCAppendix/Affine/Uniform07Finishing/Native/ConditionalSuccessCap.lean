import FCAppendix.Game.CommonListSeeds
import FCAppendix.Finite.ConditionalCountLaw

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing.ConditionalSuccess

open MeasureTheory ProbabilityTheory Bayes Game Set Filter
open scoped BigOperators

variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

def localSeedAcceptance (Γ : FiniteGame m n c Seed) (j : Fin n)
    (L : LocalList m) (i : Fin m) : ℝ :=
  Γ.seedLaw.real {s | i ∈ (Γ.policy j L s).val}

lemma measurableSet_local_acceptance (Γ : FiniteGame m n c Seed) (j : Fin n)
    (L : LocalList m) (i : Fin m) :
    MeasurableSet {s | i ∈ (Γ.policy j L s).val} :=
  (measurable_policy_at_list Γ j L)
    (MeasurableSet.of_discrete : MeasurableSet {S : Finset (Fin m) | i ∈ S})

lemma localSeedAcceptance_eq_integral (Γ : FiniteGame m n c Seed) (j : Fin n)
    (L : LocalList m) (i : Fin m) :
    localSeedAcceptance Γ j L i =
      ∫s, (if i ∈ (Γ.policy j L s).val then (1 : ℝ) else 0) ∂Γ.seedLaw := by
  classical
  symm
  simpa only [localSeedAcceptance, Set.indicator, Set.mem_setOf_eq, Pi.one_apply] using
    integral_indicator_one (μ := Γ.seedLaw) (measurableSet_local_acceptance Γ j L i)

lemma localSeedAcceptance_nonneg (Γ : FiniteGame m n c Seed) (j : Fin n)
    (L : LocalList m) (i : Fin m) : 0 ≤ localSeedAcceptance Γ j L i :=
  ENNReal.toReal_nonneg

lemma localSeedAcceptance_le_one (Γ : FiniteGame m n c Seed) (j : Fin n)
    (L : LocalList m) (i : Fin m) : localSeedAcceptance Γ j L i ≤ 1 := by
  have h := ENNReal.toReal_mono (measure_ne_top Γ.seedLaw Set.univ)
    (measure_mono (Set.subset_univ {s | i ∈ (Γ.policy j L s).val}))
  simpa only [localSeedAcceptance, measureReal_def, measure_univ, ENNReal.toReal_one] using h

omit [MeasurableSpace Seed] in
lemma inclusionCount_zero_iff_all_reject (x : Realization m n)
    (policy : Fin n → LocalPolicy m c Seed) (s : Fin n → Seed) (i : Fin m) :
    inclusionCount x policy s i = 0 ↔
      ∀ j, i ∉ (policy j (observe x j) (s j)).val := by
  classical
  simp [inclusionCount, accepted, allocation, Finset.filter_eq_empty_iff]

theorem private_seed_failure_product (Γ : FiniteGame m n c Seed)
    (x : Realization m n) (i : Fin m) :
    (∫s : Fin n → Seed,
      (if inclusionCount x Γ.policy s i = 0 then (1 : ℝ) else 0)
        ∂Measure.pi (fun _ : Fin n => Γ.seedLaw)) =
      ∏ j, (1 - localSeedAcceptance Γ j (observe x j) i) := by
  classical
  let E : Fin n → Set Seed := fun j => {s | i ∈ (Γ.policy j (observe x j) s).val}
  have hE : ∀ j, MeasurableSet (E j) := fun j =>
    measurableSet_local_acceptance Γ j (observe x j) i
  have hrect : {s : Fin n → Seed | inclusionCount x Γ.policy s i = 0} =
      Set.univ.pi (fun j => (E j)ᶜ) := by
    ext s
    simp [inclusionCount_zero_iff_all_reject, E]
  have hset : {s : Fin n → Seed | inclusionCount x Γ.policy s i = 0} =
      ⋂ j, (fun s : Fin n → Seed => s j) ⁻¹' (E j)ᶜ := by
    ext s
    simp [inclusionCount_zero_iff_all_reject, E]
  have hmeas : MeasurableSet {s : Fin n → Seed | inclusionCount x Γ.policy s i = 0} := by
    rw [hset]
    exact MeasurableSet.iInter (fun j => (hE j).compl.preimage (measurable_pi_apply j))
  calc
    _ = (Measure.pi (fun _ : Fin n => Γ.seedLaw)).real
        {s | inclusionCount x Γ.policy s i = 0} := by
      simpa only [Set.indicator, Set.mem_setOf_eq, Pi.one_apply] using
        integral_indicator_one (μ := Measure.pi (fun _ : Fin n => Γ.seedLaw)) hmeas
    _ = ∏ j, Γ.seedLaw.real ((E j)ᶜ) := by
      rw [hrect]
      simp only [measureReal_def, Measure.pi_pi, ENNReal.toReal_prod]
    _ = _ := by
      apply Finset.prod_congr rfl
      intro j _
      simpa only [localSeedAcceptance, E, probReal_univ] using
        measureReal_compl (μ := Γ.seedLaw) (hE j)

def deviationList (i : Fin m) (a : JointAction n) (d : UserProfile m n)
    (τ : Equiv.Perm (Fin n)) (j : Fin n) : LocalList m :=
  observe (deviate (drawsRealization d) i a.bid a.bid_nonneg (firstK τ a.routeCount)) j

def frozenFailure (Γ : FiniteGame m n c Seed) (i : Fin m) (a : JointAction n)
    (τ : Equiv.Perm (Fin n)) (d : UserProfile m n) : ℝ :=
  ∫s : Fin n → Seed,
    (if (focalCount Γ i a ((d, s), τ)).val = 0 then (1 : ℝ) else 0)
      ∂Measure.pi (fun _ : Fin n => Γ.seedLaw)

lemma measurable_frozenFailure (Γ : FiniteGame m n c Seed) (i : Fin m)
    (a : JointAction n) (τ : Equiv.Perm (Fin n)) :
    Measurable (frozenFailure Γ i a τ) := by
  classical
  have hcount : Measurable (fun b : Background m n Seed => focalCount Γ i a (b, τ)) :=
    (measurable_focalCount Γ i a).comp (measurable_id.prodMk measurable_const)
  have hfun : Measurable (fun b : Background m n Seed =>
      if (focalCount Γ i a (b, τ)).val = 0 then (1 : ℝ) else 0) :=
    (measurable_of_countable (fun r : Fin (n + 1) =>
      if r.val = 0 then (1 : ℝ) else 0)).comp hcount
  exact hfun.stronglyMeasurable.integral_prod_right'.measurable

lemma frozenFailure_nonneg (Γ : FiniteGame m n c Seed) (i : Fin m)
    (a : JointAction n) (τ : Equiv.Perm (Fin n)) (d : UserProfile m n) :
    0 ≤ frozenFailure Γ i a τ d :=
  integral_nonneg (fun _ => by split_ifs <;> norm_num)

lemma frozenFailure_le_one (Γ : FiniteGame m n c Seed) (i : Fin m)
    (a : JointAction n) (τ : Equiv.Perm (Fin n)) (d : UserProfile m n) :
    frozenFailure Γ i a τ d ≤ 1 := by
  classical
  have hcount : Measurable (fun s : Fin n → Seed => focalCount Γ i a ((d, s), τ)) :=
    (measurable_focalCount Γ i a).comp
      ((measurable_const.prodMk measurable_id).prodMk measurable_const)
  have hi := CountLaw.integrable_comp (Measure.pi (fun _ : Fin n => Γ.seedLaw))
    _ hcount (fun r => if r.val = 0 then (1 : ℝ) else 0)
  have h := integral_mono hi (integrable_const (1 : ℝ))
    (fun s => by split_ifs <;> norm_num)
  simpa only [frozenFailure, integral_const, probReal_univ, one_smul] using h

lemma integrable_frozenFailure (Γ : FiniteGame m n c Seed) (i : Fin m)
    (a : JointAction n) (τ : Equiv.Perm (Fin n)) :
    Integrable (frozenFailure Γ i a τ) (userProfileLaw Γ) := by
  apply Integrable.of_bound (measurable_frozenFailure Γ i a τ).aestronglyMeasurable 1
  exact Eventually.of_forall (fun d => by
    rw [Real.norm_eq_abs, abs_of_nonneg (frozenFailure_nonneg Γ i a τ d)]
    exact frozenFailure_le_one Γ i a τ d)

theorem frozenFailure_eq_product (Γ : FiniteGame m n c Seed) (i : Fin m)
    (a : JointAction n) (τ : Equiv.Perm (Fin n)) (d : UserProfile m n) :
    frozenFailure Γ i a τ d =
      ∏ j, (1 - localSeedAcceptance Γ j (deviationList i a d τ j) i) := by
  exact private_seed_failure_product Γ
    (deviate (drawsRealization d) i a.bid a.bid_nonneg (firstK τ a.routeCount)) i

theorem actual_failure_eq_profile_seed_integral (Γ : FiniteGame m n c Seed)
    (i : Fin m) (a : JointAction n) :
    1 - ((problem Γ i).outcome a).success =
      ∫τ, ∫d, frozenFailure Γ i a τ d ∂userProfileLaw Γ ∂permLaw n := by
  classical
  let f : Sample m n Seed → ℝ :=
    fun ω => if (focalCount Γ i a ω).val = 0 then 1 else 0
  have hi : Integrable f (sampleLaw Γ) :=
    CountLaw.integrable_comp _ _ (measurable_focalCount Γ i a)
      (fun r => if r.val = 0 then (1 : ℝ) else 0)
  have htest : (fun r : Fin (n + 1) => 1 - successIndicator r.val) =
      (fun r => if r.val = 0 then (1 : ℝ) else 0) := by
    funext r
    by_cases hr : r.val = 0 <;> simp [successIndicator, hr]
  calc
    _ = ((problem Γ i).outcome a).expect
        (fun r => if r.val = 0 then (1 : ℝ) else 0) := by
      rw [← htest, FiniteLaw.expect_sub, FiniteLaw.expect_const]
      rfl
    _ = ∫ω, f ω ∂sampleLaw Γ := by
      rw [problem_outcome, CountLaw.expect_ofMeasure]
    _ = ∫τ, ∫b, f (b, τ) ∂backgroundLaw Γ ∂permLaw n :=
      integral_prod_symm f hi
    _ = _ := by
      apply integral_congr_ae
      apply Eventually.of_forall
      intro τ
      change (∫b, f (b, τ) ∂(userProfileLaw Γ).prod
        (Measure.pi (fun _ : Fin n => Γ.seedLaw))) = _
      apply integral_prod
      exact CountLaw.integrable_comp _ _
        ((measurable_focalCount Γ i a).comp (measurable_id.prodMk measurable_const))
        (fun r => if r.val = 0 then (1 : ℝ) else 0)

theorem frozenFailure_ge_square (Γ : FiniteGame m 2 c Seed) (i : Fin m)
    (a : JointAction 2) (τ : Equiv.Perm (Fin 2)) (d : UserProfile m 2)
    {p : ℝ} (hp : p ≤ 1)
    (hlocal : ∀ j, localSeedAcceptance Γ j (deviationList i a d τ j) i ≤ p) :
    (1 - p) ^ 2 ≤ frozenFailure Γ i a τ d := by
  rw [frozenFailure_eq_product, Fin.prod_univ_two]
  have h0 : 1 - p ≤ 1 - localSeedAcceptance Γ 0 (deviationList i a d τ 0) i := by
    linarith [hlocal 0]
  have h1 : 1 - p ≤ 1 - localSeedAcceptance Γ 1 (deviationList i a d τ 1) i := by
    linarith [hlocal 1]
  have hb : 0 ≤ 1 - p := sub_nonneg.mpr hp
  simpa only [pow_two] using mul_le_mul h0 h1 hb (hb.trans h0)

theorem actual_success_le_good_event (Γ : FiniteGame m 2 c Seed)
    (i : Fin m) (a : JointAction 2) (G : Set (UserProfile m 2))
    (hG : MeasurableSet G) {p : ℝ} (hp : p ≤ 1)
    (hgood : ∀ᵐ d ∂userProfileLaw Γ, d ∈ G →
      ∀ τ j, localSeedAcceptance Γ j (deviationList i a d τ j) i ≤ p) :
    ((problem Γ i).outcome a).success ≤
      1 - (1 - p) ^ 2 * (userProfileLaw Γ).real G := by
  classical
  have hprofile (τ : Equiv.Perm (Fin 2)) :
      (1 - p) ^ 2 * (userProfileLaw Γ).real G ≤
        ∫d, frozenFailure Γ i a τ d ∂userProfileLaw Γ := by
    have hint : Integrable (fun d => (1 - p) ^ 2 * G.indicator (1 : UserProfile m 2 → ℝ) d)
        (userProfileLaw Γ) :=
      ((integrable_const (1 : ℝ)).indicator hG).const_mul ((1 - p) ^ 2)
    have h := integral_mono_ae hint (integrable_frozenFailure Γ i a τ) (by
      filter_upwards [hgood] with d hd
      by_cases hdG : d ∈ G
      · simp only [Set.indicator_of_mem hdG, Pi.one_apply, mul_one]
        exact frozenFailure_ge_square Γ i a τ d hp (hd hdG τ)
      · simp only [Set.indicator_of_notMem hdG, mul_zero]
        exact frozenFailure_nonneg Γ i a τ d)
    rwa [integral_const_mul, integral_indicator_one hG] at h
  have hi : Integrable (fun τ => ∫d, frozenFailure Γ i a τ d ∂userProfileLaw Γ)
      (permLaw 2) := by
    apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable 1
    apply Eventually.of_forall
    intro τ
    have h0 : 0 ≤ ∫d, frozenFailure Γ i a τ d ∂userProfileLaw Γ :=
      integral_nonneg (frozenFailure_nonneg Γ i a τ)
    have h1 : (∫d, frozenFailure Γ i a τ d ∂userProfileLaw Γ) ≤ 1 := by
      have h := integral_mono (integrable_frozenFailure Γ i a τ)
        (integrable_const (1 : ℝ)) (frozenFailure_le_one Γ i a τ)
      simpa only [integral_const, probReal_univ, one_smul] using h
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    exact h1
  have h := integral_mono (integrable_const ((1 - p) ^ 2 * (userProfileLaw Γ).real G))
    hi hprofile
  simp only [integral_const, probReal_univ, one_smul] at h
  rw [← actual_failure_eq_profile_seed_integral] at h
  linarith

theorem actual_success_le_of_bad_mass (Γ : FiniteGame m 2 c Seed)
    (i : Fin m) (a : JointAction 2) (G : Set (UserProfile m 2))
    (hG : MeasurableSet G) {p ε : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hbad : (userProfileLaw Γ).real Gᶜ ≤ ε)
    (hgood : ∀ᵐ d ∂userProfileLaw Γ, d ∈ G →
      ∀ τ j, localSeedAcceptance Γ j (deviationList i a d τ j) i ≤ p) :
    ((problem Γ i).outcome a).success ≤ 1 - (1 - p) ^ 2 + ε := by
  have h := actual_success_le_good_event Γ i a G hG hp1 hgood
  have hc : (userProfileLaw Γ).real Gᶜ = 1 - (userProfileLaw Γ).real G := by
    simpa only [probReal_univ] using measureReal_compl (μ := userProfileLaw Γ) hG
  have hs : (1 - p) ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg hp0 (sub_nonneg.mpr hp1)]
  have hmul := mul_le_mul_of_nonneg_right hs
    (show 0 ≤ (userProfileLaw Γ).real Gᶜ from ENNReal.toReal_nonneg)
  rw [one_mul] at hmul
  rw [hc] at hmul
  nlinarith

theorem actual_success_le_half_gap (Γ : FiniteGame m 2 c Seed)
    (i : Fin m) (a : JointAction 2) (G : Set (UserProfile m 2))
    (hG : MeasurableSet G) {p ε : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1)
    (hbad : (userProfileLaw Γ).real Gᶜ ≤ ε)
    (hε : ε ≤ (1 - p) ^ 2 / 2)
    (hgood : ∀ᵐ d ∂userProfileLaw Γ, d ∈ G →
      ∀ τ j, localSeedAcceptance Γ j (deviationList i a d τ j) i ≤ p) :
    ((problem Γ i).outcome a).success ≤ 1 - (1 - p) ^ 2 / 2 ∧
      1 - (1 - p) ^ 2 / 2 < 1 := by
  have h := actual_success_le_of_bad_mass Γ i a G hG hp0 hp1.le hbad hgood
  have hs : 0 < (1 - p) ^ 2 := sq_pos_of_pos (sub_pos.mpr hp1)
  constructor <;> linarith

theorem all_lower_contracts_success_cap (Γ : FiniteGame m 2 c Seed)
    (B : Set (JointAction 2)) {p ε : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1)
    (hε : ε ≤ (1 - p) ^ 2 / 2)
    (hgood : ∀ i a, a ∈ B → ∃ G : Set (UserProfile m 2),
      MeasurableSet G ∧ (userProfileLaw Γ).real Gᶜ ≤ ε ∧
      ∀ᵐ d ∂userProfileLaw Γ, d ∈ G →
        ∀ τ j, localSeedAcceptance Γ j (deviationList i a d τ j) i ≤ p) :
    (∀ i a, a ∈ B →
      ((problem Γ i).outcome a).success ≤ 1 - (1 - p) ^ 2 / 2) ∧
      1 - (1 - p) ^ 2 / 2 < 1 := by
  constructor
  · intro i a ha
    obtain ⟨G, hG, hbad, hlocal⟩ := hgood i a ha
    exact (actual_success_le_half_gap Γ i a G hG hp0 hp1 hbad hε hlocal).1
  · have hs : 0 < (1 - p) ^ 2 := sq_pos_of_pos (sub_pos.mpr hp1)
    linarith

theorem conditional_success_le_of_action_caps (Γ : FiniteGame m 2 c Seed)
    (hm : 0 < m) (v : ℝ) (B : Set (JointAction 2))
    (hsupport : ∀ᵐ a ∂Γ.σ v, a ∈ B) {s : ℝ}
    (hcap : ∀ i a, a ∈ B → ((problem Γ i).outcome a).success ≤ s) :
    (conditionalTypeCountLaw Γ hm v).success ≤ s := by
  have hi (i : Fin m) :
      Integrable (fun a => ((problem Γ i).outcome a).success) (Γ.σ v) :=
    FiniteLaw.integrable_expect (Γ.σ v) (problem Γ i).outcome
      (measurable_outcome_mass Γ i) (fun r => successIndicator r.val)
  have hmean (i : Fin m) :
      (∫a, ((problem Γ i).outcome a).success ∂Γ.σ v) ≤ s := by
    have h := integral_mono_ae (hi i) (integrable_const s) (by
      filter_upwards [hsupport] with a ha
      exact hcap i a ha)
    simpa only [integral_const, probReal_univ, one_smul] using h
  rw [conditionalTypeCountLaw_success]
  apply (div_le_iff₀ (show (0 : ℝ) < m by exact_mod_cast hm)).mpr
  calc
    _ ≤ ∑ _i : Fin m, s := Finset.sum_le_sum (fun i _ => hmean i)
    _ = s * m := by simp [mul_comm]

theorem conditional_success_cap_all_values_of_actionwise_events
    (Γ : FiniteGame m 2 c Seed) (hm : 0 < m)
    (V : Set ℝ) (B : Set (JointAction 2))
    (hsupport : ∀ v ∈ V, ∀ᵐ a ∂Γ.σ v, a ∈ B)
    {p ε : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1) (hε : ε ≤ (1 - p) ^ 2 / 2)
    (hgood : ∀ i a, a ∈ B → ∃ G : Set (UserProfile m 2),
      MeasurableSet G ∧ (userProfileLaw Γ).real Gᶜ ≤ ε ∧
      ∀ᵐ d ∂userProfileLaw Γ, d ∈ G →
        ∀ τ j, localSeedAcceptance Γ j (deviationList i a d τ j) i ≤ p) :
    (∀ v ∈ V, (conditionalTypeCountLaw Γ hm v).success ≤ 1 - (1 - p) ^ 2 / 2) ∧
      1 - (1 - p) ^ 2 / 2 < 1 := by
  obtain ⟨hcap, hstrict⟩ := all_lower_contracts_success_cap Γ B hp0 hp1 hε hgood
  exact ⟨fun v hv => conditional_success_le_of_action_caps Γ hm v B
    (hsupport v hv) hcap, hstrict⟩

theorem conditional_success_le_of_bad_mass (Γ : FiniteGame m 2 c Seed)
    (hm : 0 < m) (v : ℝ) (B : Set (JointAction 2))
    (hsupport : ∀ᵐ a ∂Γ.σ v, a ∈ B)
    (G : Set (UserProfile m 2)) (hG : MeasurableSet G)
    {p ε : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hbad : (userProfileLaw Γ).real Gᶜ ≤ ε)
    (hgood : ∀ᵐ d ∂userProfileLaw Γ, d ∈ G →
      ∀ i a, a ∈ B → ∀ τ j,
        localSeedAcceptance Γ j (deviationList i a d τ j) i ≤ p) :
    (conditionalTypeCountLaw Γ hm v).success ≤ 1 - (1 - p) ^ 2 + ε := by
  have hi (i : Fin m) :
      Integrable (fun a => ((problem Γ i).outcome a).success) (Γ.σ v) :=
    FiniteLaw.integrable_expect (Γ.σ v) (problem Γ i).outcome
      (measurable_outcome_mass Γ i) (fun r => successIndicator r.val)
  have hmean (i : Fin m) :
      (∫a, ((problem Γ i).outcome a).success ∂Γ.σ v) ≤ 1 - (1 - p) ^ 2 + ε := by
    have h := integral_mono_ae (hi i) (integrable_const (1 - (1 - p) ^ 2 + ε)) (by
      filter_upwards [hsupport] with a ha
      apply actual_success_le_of_bad_mass Γ i a G hG hp0 hp1 hbad
      filter_upwards [hgood] with d hd
      intro hdG
      exact hd hdG i a ha)
    simpa only [integral_const, probReal_univ, one_smul] using h
  rw [conditionalTypeCountLaw_success]
  apply (div_le_iff₀ (show (0 : ℝ) < m by exact_mod_cast hm)).mpr
  calc
    _ ≤ ∑ _i : Fin m, (1 - (1 - p) ^ 2 + ε) :=
      Finset.sum_le_sum (fun i _ => hmean i)
    _ = (1 - (1 - p) ^ 2 + ε) * m := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

theorem conditional_success_cap_all_values (Γ : FiniteGame m 2 c Seed)
    (hm : 0 < m) (V : Set ℝ) (B : Set (JointAction 2))
    (hsupport : ∀ v ∈ V, ∀ᵐ a ∂Γ.σ v, a ∈ B)
    (G : Set (UserProfile m 2)) (hG : MeasurableSet G)
    {p ε : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1)
    (hbad : (userProfileLaw Γ).real Gᶜ ≤ ε)
    (hε : ε ≤ (1 - p) ^ 2 / 2)
    (hgood : ∀ᵐ d ∂userProfileLaw Γ, d ∈ G →
      ∀ i a, a ∈ B → ∀ τ j,
        localSeedAcceptance Γ j (deviationList i a d τ j) i ≤ p) :
    (∀ v ∈ V, (conditionalTypeCountLaw Γ hm v).success ≤ 1 - (1 - p) ^ 2 / 2) ∧
      1 - (1 - p) ^ 2 / 2 < 1 := by
  constructor
  · intro v hv
    have h := conditional_success_le_of_bad_mass Γ hm v B (hsupport v hv)
      G hG hp0 hp1.le hbad hgood
    linarith
  · have hs : 0 < (1 - p) ^ 2 := sq_pos_of_pos (sub_pos.mpr hp1)
    linarith

end FCAppendix.Affine.Uniform07Finishing.ConditionalSuccess
