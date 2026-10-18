import FCAppendix.Proposer.MeasurableExactCapacity
import FCAppendix.Game.PosteriorBeliefs
import FCAppendix.Probability.FinitePushforward

noncomputable section
namespace FCAppendix.FiniteLaw
open MeasureTheory Set
open scoped BigOperators
variable {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

theorem probabilityMeasure_ae_mass_ne_zero (μ : FiniteLaw Ω) :
    ∀ᵐ ω ∂probabilityMeasure μ, μ.mass ω ≠ 0 := by
  classical
  rw [ae_iff]
  simp only [not_not]
  change probabilityMeasure μ {ω | μ.mass ω = 0} = 0
  simp only [probabilityMeasure, Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
  apply Finset.sum_eq_zero
  intro ω _
  by_cases hω : μ.mass ω = 0
  · simp [hω]
  · simp [Measure.dirac_apply, Set.indicator, hω]

theorem marginal_pos_of_support_mem {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : FiniteLaw (Finset ι)) (S : Finset ι) (hS : μ.mass S ≠ 0)
    (i : ι) (hi : i ∈ S) : 0 < μ.prob (fun T => i ∈ T) := by
  rw [prob_eq_expect]
  unfold expect
  have hs : 0 < μ.mass S := lt_of_le_of_ne (μ.nonneg S) hS.symm
  apply lt_of_lt_of_le hs
  have hh := Finset.single_le_sum
    (f := fun T : Finset ι => μ.mass T * (if i ∈ T then (1 : ℝ) else 0))
    (fun T _ => mul_nonneg (μ.nonneg T) (by split <;> norm_num)) (Finset.mem_univ S)
  simpa only [if_pos hi, mul_one] using hh

theorem ofMeasure_eq_of_map_eq_probabilityMeasure
    {A : Type*} [MeasurableSpace A] (ν : Measure A) [IsProbabilityMeasure ν]
    (f : A → Ω) (hf : Measurable f) (μ : FiniteLaw Ω)
    (hmap : ν.map f = probabilityMeasure μ) : ofMeasure ν f hf = μ := by
  apply FiniteLaw.ext
  intro ω
  rw [ofMeasure_mass]
  have hs := congrArg (fun ξ : Measure Ω => ξ {ω}) hmap
  rw [Measure.map_apply hf (measurableSet_singleton ω), probabilityMeasure_singleton] at hs
  change (ν (f ⁻¹' {ω})).toReal = μ.mass ω
  rw [hs, ENNReal.toReal_ofReal (μ.nonneg ω)]

end FCAppendix.FiniteLaw

namespace FCAppendix.Game
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
variable {m c : ℕ}

def LocallyFeasible (L : LocalList m) (c : ℕ) (S : Finset (Fin m)) : Prop :=
  S.card ≤ c ∧ ∀ i ∈ S, L i ≠ none

lemma measurableSet_locallyFeasible :
    MeasurableSet {x : LocalList m × Finset (Fin m) | LocallyFeasible x.1 c x.2} := by
  classical
  have hcard : MeasurableSet {x : LocalList m × Finset (Fin m) | x.2.card ≤ c} :=
    (measurable_of_countable (fun S : Finset (Fin m) => S.card ≤ c)).comp
      measurable_snd |>.setOf
  have hvisible : MeasurableSet {x : LocalList m × Finset (Fin m) |
      ∀ i : Fin m, i ∈ x.2 → x.1 i ≠ none} := by
    have he : {x : LocalList m × Finset (Fin m) |
        ∀ i : Fin m, i ∈ x.2 → x.1 i ≠ none} =
        ⋂ i : Fin m, {x | i ∉ x.2 ∨ x.1 i ≠ none} := by
      ext x
      simp only [mem_setOf_eq, mem_iInter, imp_iff_not_or]
    rw [he]
    apply MeasurableSet.iInter
    intro i
    apply MeasurableSet.union
    · exact ((measurable_of_countable (fun S : Finset (Fin m) => i ∈ S)).comp
        measurable_snd).setOf.compl
    · have hv : Measurable (fun x : LocalList m × Finset (Fin m) => x.1 i) :=
        (measurable_pi_apply i).comp measurable_fst
      exact (measurableSet_eq_fun hv measurable_const).compl
  exact hcard.inter hvisible

theorem symmetricLottery_support_locallyFeasible (L : LocalList m)
    (p : Fin m → ℝ) (d : ℕ) (hd : d ≤ c)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) (hsum : ∑ i, p i = d)
    (habsent : ∀ i, L i = none → p i = 0) :
    ∀ S, (ExactCapacity.symmetricLottery p).mass S ≠ 0 → LocallyFeasible L c S := by
  have h := ExactCapacity.symmetricLottery_implements p d hp0 hp1 hsum
  intro S hS
  refine ⟨(h.1 S hS).le.trans hd, ?_⟩
  intro i hi hab
  have hpos := FiniteLaw.marginal_pos_of_support_mem _ S hS i hi
  rw [h.2 i, habsent i hab] at hpos
  exact (lt_irrefl 0) hpos

theorem exists_measurable_localPolicy
    (p : LocalList m → Fin m → ℝ) (hp : Measurable p)
    (d : LocalList m → ℕ) (hd : ∀ L, d L ≤ c)
    (hp0 : ∀ L i, 0 ≤ p L i) (hp1 : ∀ L i, p L i ≤ 1)
    (hsum : ∀ L, ∑ i, p L i = d L)
    (habsent : ∀ L i, L i = none → p L i = 0) :
    ∃ policy : LocalPolicy m c unitInterval,
      Measurable (fun x : LocalList m × unitInterval => (policy x.1 x.2).val) ∧
      ∀ L, volume.map (fun u => (policy L u).val) =
        FiniteLaw.probabilityMeasure (ExactCapacity.symmetricLottery (p L)) := by
  classical
  obtain ⟨sample, hsample, hsampleLaw⟩ := ExactCapacity.exists_symmetricLottery_sampler (ι := Fin m)
  let raw : LocalList m → unitInterval → Finset (Fin m) := fun L u => sample (p L) u
  have hraw : Measurable (Function.uncurry raw) :=
    hsample.comp ((hp.comp measurable_fst).prodMk measurable_snd)
  have hvalid : MeasurableSet {x : LocalList m × unitInterval |
      LocallyFeasible x.1 c (raw x.1 x.2)} :=
    measurableSet_locallyFeasible.preimage (measurable_fst.prodMk hraw)
  let policy : LocalPolicy m c unitInterval := fun L u =>
    if h : LocallyFeasible L c (raw L u) then ⟨raw L u, h⟩
      else ⟨∅, by simp⟩
  have hpolicy : Measurable (fun x : LocalList m × unitInterval => (policy x.1 x.2).val) := by
    convert Measurable.ite hvalid hraw (measurable_const (a := (∅ : Finset (Fin m)))) using 1
    funext x
    simp only [policy]
    split <;> rfl
    exact fun _ => Classical.propDecidable _
  refine ⟨policy, hpolicy, ?_⟩
  intro L
  have hsupport := FiniteLaw.probabilityMeasure_ae_mass_ne_zero
    (ExactCapacity.symmetricLottery (p L))
  have hrawLaw : volume.map (raw L) =
      FiniteLaw.probabilityMeasure (ExactCapacity.symmetricLottery (p L)) := hsampleLaw (p L)
  have hrawmeas : Measurable (raw L) := hraw.comp (measurable_const.prodMk measurable_id)
  have hgood : ∀ᵐ u ∂(volume : Measure unitInterval), LocallyFeasible L c (raw L u) := by
    rw [← hrawLaw] at hsupport
    have hh := (ae_map_iff hrawmeas.aemeasurable (by measurability)).mp hsupport
    filter_upwards [hh] with u hu
    exact symmetricLottery_support_locallyFeasible L (p L) (d L) (hd L)
      (hp0 L) (hp1 L) (hsum L) (habsent L) _ hu
  have heq : (fun u => (policy L u).val) =ᵐ[(volume : Measure unitInterval)] raw L := by
    filter_upwards [hgood] with u hu
    simp only [policy, dif_pos hu]
  exact (Measure.map_congr heq).trans hrawLaw

theorem exists_measurable_localPolicy_finiteLaw
    (p : LocalList m → Fin m → ℝ) (hp : Measurable p)
    (d : LocalList m → ℕ) (hd : ∀ L, d L ≤ c)
    (hp0 : ∀ L i, 0 ≤ p L i) (hp1 : ∀ L i, p L i ≤ 1)
    (hsum : ∀ L, ∑ i, p L i = d L)
    (habsent : ∀ L i, L i = none → p L i = 0) :
    ∃ (policy : LocalPolicy m c unitInterval)
      (hpolicy : Measurable (fun x : LocalList m × unitInterval => (policy x.1 x.2).val)),
      ∀ L, FiniteLaw.ofMeasure volume (fun u => (policy L u).val)
        (hpolicy.comp (measurable_const.prodMk measurable_id)) =
        ExactCapacity.symmetricLottery (p L) := by
  obtain ⟨policy,hpolicy,hlaw⟩ := exists_measurable_localPolicy p hp d hd hp0 hp1 hsum habsent
  exact ⟨policy,hpolicy,fun L =>
    FiniteLaw.ofMeasure_eq_of_map_eq_probabilityMeasure _ _ _ _ (hlaw L)⟩

end FCAppendix.Game
