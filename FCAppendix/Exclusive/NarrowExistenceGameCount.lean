import FCAppendix.Exclusive.NarrowExistenceGameScore
import FCAppendix.Probability.EmpiricalConcentration

noncomputable section
namespace FCAppendix.Exclusive.Narrow.Existence
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped BigOperators

variable {V : Type*} [MeasurableSpace V]

theorem measurable_activeBit : Measurable activeBit := measurable_of_countable _

theorem integral_activeBit_sampleLaw (h : unitInterval) (nu : Measure V)
    [IsProbabilityMeasure nu] :
    (∫ x, activeBit x.1 ∂sampleLaw h nu) = (h : ℝ) := by
  rw [sampleLaw, integral_fun_fst, probReal_univ, one_smul,
    integral_bernoulliMeasure]
  simp [activeBit]

omit [MeasurableSpace V] in
theorem activeCount_cast {m : ℕ} (omega : RivalProfile m V) :
    (activeCount omega : ℝ) = ∑ i, activeBit (omega i).1 := by
  simp only [activeCount, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  cases (omega i).1 <;> norm_num [activeNat, activeBit]

theorem activeCount_empirical_tail (h : unitInterval) (nu : Measure V)
    [IsProbabilityMeasure nu] (m : ℕ) (hm : 0 < m) {eta : ℝ} (heta : 0 ≤ eta) :
    (iidRivalLaw m h nu).real
      {omega | eta ≤ |(activeCount omega : ℝ)/(m : ℝ)-(h : ℝ)|} ≤
      2*Real.exp (-2*(m : ℝ)*eta^2) := by
  have hb : ∀ᵐ x ∂sampleLaw h nu, activeBit x.1 ∈ Icc (0 : ℝ) 1 :=
    Eventually.of_forall fun x => by cases x.1 <;> norm_num [activeBit]
  have ht := Probability.iid_empiricalMean_two_sided_le (sampleLaw h nu)
    (measurable_activeBit.comp measurable_fst).aemeasurable hb m hm heta
  simpa only [Function.comp_apply, integral_activeBit_sampleLaw,
    ← activeCount_cast, iidRivalLaw] using ht

theorem forced_fraction_gap {m C : ℕ} (hm : 0 < m) (hC : C ≤ m) :
    |(1+(C : ℝ))/((m : ℝ)+1)-(C : ℝ)/(m : ℝ)| ≤ 1/((m : ℝ)+1) := by
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hCR : (C : ℝ) ≤ m := by exact_mod_cast hC
  have he : (1+(C : ℝ))/((m : ℝ)+1)-(C : ℝ)/(m : ℝ) =
      ((m : ℝ)-(C : ℝ))/((m : ℝ)*((m : ℝ)+1)) := by
    field_simp
    ring
  rw [he, abs_of_nonneg (by positivity)]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith [show (0 : ℝ) ≤ C by positivity]

theorem forcedActiveFraction_two_sided_le (h : unitInterval) (nu : Measure V)
    [IsProbabilityMeasure nu] (m : ℕ) (hm : 0 < m) {eta : ℝ} (heta : 0 < eta)
    (hsmall : 1/((m : ℝ)+1) ≤ eta/2) :
    (iidRivalLaw m h nu).real
      {omega | eta ≤ |(1+(activeCount omega : ℝ))/((m : ℝ)+1)-(h : ℝ)|} ≤
      2*Real.exp (-2*(m : ℝ)*(eta/2)^2) := by
  have hs : {omega : RivalProfile m V |
      eta ≤ |(1+(activeCount omega : ℝ))/((m : ℝ)+1)-(h : ℝ)|} ⊆
      {omega | eta/2 ≤ |(activeCount omega : ℝ)/(m : ℝ)-(h : ℝ)|} := by
    intro omega ho
    have hg := forced_fraction_gap hm (activeCount_le omega)
    have ht := abs_sub_le ((1+(activeCount omega : ℝ))/((m : ℝ)+1))
      ((activeCount omega : ℝ)/(m : ℝ)) (h : ℝ)
    dsimp only [mem_setOf_eq] at ho ⊢
    linarith
  exact (measureReal_mono hs).trans
    (activeCount_empirical_tail h nu m hm (by positivity))

theorem exists_count_bad_probability_bound (h : unitInterval)
    {eta probability : ℝ} (heta : 0 < eta) (hprobability : 0 < probability) :
    ∃ M0 : ℕ, ∀ m ≥ M0, ∀ (nu : Measure V) [IsProbabilityMeasure nu],
      (iidRivalLaw m h nu).real
        {omega | eta ≤ |(1+(activeCount omega : ℝ))/((m : ℝ)+1)-(h : ℝ)|} <
        probability := by
  have hinv : Tendsto (fun m : ℕ => 1/((m : ℝ)+1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hexp : Tendsto (fun m : ℕ => 2*Real.exp (-2*(m : ℝ)*(eta/2)^2))
      atTop (𝓝 0) := by
    have hp : 0 < 2*(eta/2)^2 := by positivity
    have ht := Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_natCast_atTop_atTop.const_mul_atTop hp)
    simpa only [Function.comp_def, mul_zero, show ∀ x : ℝ,
      -(2*(eta/2)^2*x) = -2*x*(eta/2)^2 by intro x; ring] using ht.const_mul 2
  obtain ⟨M0, hM0⟩ := eventually_atTop.mp
    ((hinv.eventually_le_const (by positivity : (0 : ℝ) < eta/2)).and
      ((hexp.eventually_lt_const hprobability).and (eventually_ge_atTop 1)))
  refine ⟨M0, ?_⟩
  intro m hm nu _
  exact (forcedActiveFraction_two_sided_le h nu m (by have := (hM0 m hm).2.2; omega)
    heta (hM0 m hm).1).trans_lt (hM0 m hm).2.1

end FCAppendix.Exclusive.Narrow.Existence
