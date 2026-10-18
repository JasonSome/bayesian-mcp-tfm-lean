import FCAppendix.Exclusive.ActionLawTransport
import FCAppendix.Exclusive.NarrowExistenceGameCount

noncomputable section
namespace FCAppendix.Bayes.ExclusiveSource
open MeasureTheory ProbabilityTheory Game Exclusive Set Filter Topology
open Exclusive.Narrow.Existence ExclusiveConstruction
open scoped BigOperators

variable {m n c : ℕ} {Seed V : Type*} [MeasurableSpace Seed] [MeasurableSpace V]

def submissions (a : Fin m → JointAction n) : ℕ :=
  ∑ j, if (a j).routeCount = 0 then 0 else 1

theorem measurable_submissions : Measurable (submissions (m := m) (n := n)) := by
  let f : (Fin m → ℕ) → ℕ := fun k => ∑ j, if k j = 0 then 0 else 1
  exact (measurable_of_countable f).comp
    (measurable_pi_lambda _ fun j => (measurable_routeCount n).comp (measurable_pi_apply j))

def submittedRivals (i : Fin (m+1)) (d : UserProfile (m+1) n) : ℕ :=
  submissions (fun j => (d (i.succAbove j)).1.2)

theorem measurable_submittedRivals (i : Fin (m+1)) :
    Measurable (submittedRivals (n := n) i) :=
  measurable_submissions.comp (measurable_pi_lambda _ fun j =>
    measurable_snd.comp (measurable_fst.comp (measurable_pi_apply (i.succAbove j))))

omit [MeasurableSpace V] in
theorem submissions_flagAction (hn : 0 < n) (b : V → ℝ) (omega : RivalProfile m V) :
    submissions (fun j => flagAction n b (omega j)) = activeCount omega := by
  classical
  unfold submissions activeCount
  apply Finset.sum_congr rfl
  intro j _
  cases hh : (omega j).1 <;> simp [flagAction,hh,Interim.abstain,activeNat,ne_of_gt hn]

theorem measurable_activeCount_profile :
    Measurable (activeCount : RivalProfile m V → ℕ) := by
  let f : (Fin m → Bool) → ℕ := fun z => ∑ j, activeNat (z j)
  exact (measurable_of_countable f).comp
    (measurable_pi_lambda _ fun j => measurable_fst.comp (measurable_pi_apply j))

theorem submittedRivals_law (Γ : FiniteGame (m+1) n c Seed)
    (i : Fin (m+1)) (hn : 0 < n) (h : unitInterval) (nu : Measure V)
    [IsProbabilityMeasure nu] (b : V → ℝ) (hb : Measurable b)
    (hActions : (userProfileLaw Γ).map (fun d j => (d (i.succAbove j)).1.2) =
      (iidRivalLaw m h nu).map (fun omega j => flagAction n b (omega j))) :
    (userProfileLaw Γ).map (submittedRivals i) =
      (iidRivalLaw m h nu).map activeCount := by
  have hp : Measurable (fun d : UserProfile (m+1) n => fun j : Fin m =>
      (d (i.succAbove j)).1.2) := measurable_pi_lambda _ fun j =>
    measurable_snd.comp (measurable_fst.comp (measurable_pi_apply (i.succAbove j)))
  have hf : Measurable (fun omega : RivalProfile m V => fun j => flagAction n b (omega j)) :=
    measurable_pi_lambda _ fun j => (measurable_flagAction n hb).comp (measurable_pi_apply j)
  change (userProfileLaw Γ).map (submissions ∘ _) = _
  rw [← Measure.map_map measurable_submissions hp,hActions,
    Measure.map_map measurable_submissions hf]
  congr 1
  funext omega
  exact submissions_flagAction hn b omega

theorem submittedRivals_forced_fraction_tail (Γ : FiniteGame (m+1) n c Seed)
    (i : Fin (m+1)) (hn : 0 < n) (h : unitInterval) (nu : Measure V)
    [IsProbabilityMeasure nu] (b : V → ℝ) (hb : Measurable b)
    (hActions : (userProfileLaw Γ).map (fun d j => (d (i.succAbove j)).1.2) =
      (iidRivalLaw m h nu).map (fun omega j => flagAction n b (omega j)))
    {eta : ℝ} (hm : 0 < m) (heta : 0 < eta)
    (hsmall : 1/((m : ℝ)+1) ≤ eta/2) :
    (userProfileLaw Γ).real
      {d | eta ≤ |(1+(submittedRivals i d : ℝ))/((m : ℝ)+1)-(h : ℝ)|} ≤
      2*Real.exp (-2*(m : ℝ)*(eta/2)^2) := by
  let T : Set ℕ := {N | eta ≤ |(1+(N : ℝ))/((m : ℝ)+1)-(h : ℝ)|}
  have hT : MeasurableSet T := (Set.to_countable _).measurableSet
  have he := congrArg (fun mu : Measure ℕ => mu.real T)
    (submittedRivals_law Γ i hn h nu b hb hActions)
  simp only [measureReal_def,Measure.map_apply (measurable_submittedRivals i) hT,
    Measure.map_apply measurable_activeCount_profile hT] at he
  change (userProfileLaw Γ).real ((submittedRivals i) ⁻¹' T) ≤ _
  rw [measureReal_def,he]
  exact forcedActiveFraction_two_sided_le h nu m hm heta hsmall

theorem exists_actual_count_bad_probability_bound (h : unitInterval)
    {eta probability : ℝ} (heta : 0 < eta) (hprobability : 0 < probability) :
    ∃ M0 : ℕ, ∀ m ≥ M0, ∀ (n c : ℕ) (Γ : FiniteGame (m+1) n c Seed)
      (i : Fin (m+1)) (_hn : 0 < n) (V : Type*) [MeasurableSpace V]
      (nu : Measure V) [IsProbabilityMeasure nu]
      (b : V → ℝ) (_hb : Measurable b),
      (userProfileLaw Γ).map (fun d j => (d (i.succAbove j)).1.2) =
        (iidRivalLaw m h nu).map (fun omega j => flagAction n b (omega j)) →
      (userProfileLaw Γ).real
        {d | eta ≤ |(1+(submittedRivals i d : ℝ))/((m : ℝ)+1)-(h : ℝ)|} <
          probability := by
  have hinv : Tendsto (fun m : ℕ => 1/((m : ℝ)+1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hexp : Tendsto (fun m : ℕ => 2*Real.exp (-2*(m : ℝ)*(eta/2)^2))
      atTop (𝓝 0) := by
    have hp : 0 < 2*(eta/2)^2 := by positivity
    have ht := Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_natCast_atTop_atTop.const_mul_atTop hp)
    simpa only [Function.comp_def,mul_zero,show ∀ x : ℝ,
      -(2*(eta/2)^2*x) = -2*x*(eta/2)^2 by intro x; ring] using ht.const_mul 2
  obtain ⟨M0,hM0⟩ := eventually_atTop.mp
    ((hinv.eventually_le_const (by positivity : (0 : ℝ) < eta/2)).and
      ((hexp.eventually_lt_const hprobability).and (eventually_ge_atTop 1)))
  refine ⟨M0,?_⟩
  intro m hm n c Γ i hn V _ nu _ b hb hActions
  exact (submittedRivals_forced_fraction_tail Γ i hn h nu b hb hActions
    (by have := (hM0 m hm).2.2; omega) heta (hM0 m hm).1).trans_lt (hM0 m hm).2.1

end FCAppendix.Bayes.ExclusiveSource
