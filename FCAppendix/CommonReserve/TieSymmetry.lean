import FCAppendix.CommonReserve.UniformTies
import FCAppendix.CommonReserve.IdentityBounds
import FCAppendix.Probability.FinitePushforward

noncomputable section
namespace FCAppendix.CommonReserve
open Game MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators

variable {m c : ℕ} {r : ℝ} {Seed : Type*} [MeasurableSpace Seed]

theorem positiveEligible_relabel (e : Equiv.Perm (Fin m)) (L : LocalList m) :
    positiveEligible (L ∘ e.symm) r = (positiveEligible L r).map e.toEmbedding := by
  classical
  ext i
  simp [positiveEligible]

theorem positiveList_relabel (e : Equiv.Perm (Fin m)) (L : LocalList m) :
    positiveList (L ∘ e.symm) r = positiveList L r ∘ e.symm := by
  classical
  funext i
  simp [positiveList, positiveEligible]

theorem optimal_relabel (e : Equiv.Perm (Fin m)) (b : Fin m → ℝ) (S : Finset (Fin m))
    (hS : Finite.Optimal c b S) :
    Finite.Optimal c (b ∘ e.symm) (S.map e.toEmbedding) := by
  classical
  refine ⟨by simpa using hS.1, ?_⟩
  intro T hT
  have hh := hS.2 (T.map e.symm.toEmbedding) (by simpa using hT)
  simpa only [Finset.sum_map, Function.comp_apply, Equiv.coe_toEmbedding,
    Equiv.symm_apply_apply] using hh

theorem TopChoice.relabel {L : LocalList m} {S : Finset (Fin m)}
    (h : TopChoice L r c S) (e : Equiv.Perm (Fin m)) :
    TopChoice (L ∘ e.symm) r c (S.map e.toEmbedding) := by
  constructor
  · rw [positiveEligible_relabel]
    exact Finset.map_subset_map.mpr h.1
  · rw [positiveList_relabel]
    exact optimal_relabel e _ _ h.2

theorem topChoices_relabel (e : Equiv.Perm (Fin m)) (L : LocalList m) :
    topChoices (L ∘ e.symm) r c = (topChoices L r c).map e.finsetCongr.toEmbedding := by
  classical
  ext S
  simp only [topChoices, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_map_equiv]
  constructor
  · intro h
    have hh := h.relabel e.symm
    simpa only [Equiv.finsetCongr_symm, Equiv.finsetCongr_apply,
      Equiv.symm_symm, Function.comp_assoc, Equiv.symm_comp_self, Function.comp_id] using hh
  · intro h
    have hh := h.relabel e
    change TopChoice (L ∘ e.symm) r c (e.finsetCongr (e.finsetCongr.symm S)) at hh
    simpa only [Equiv.apply_symm_apply] using hh

def positiveLaw (ν : Measure Seed) [IsProbabilityMeasure ν]
    (policy : LocalPolicy m c Seed)
    (hp : Measurable (fun p : LocalList m × Seed => (policy p.1 p.2).val))
    (L : LocalList m) : FiniteLaw (Finset (Fin m)) :=
  FiniteLaw.ofMeasure ν (fun s => positiveSelection L (policy L s).val)
    ((measurable_positiveSelection_policy policy hp).comp
      (measurable_const.prodMk measurable_id))

theorem positiveLaw_mass_relabel (ν : Measure Seed) [IsProbabilityMeasure ν]
    (policy : LocalPolicy m c Seed)
    (hp : Measurable (fun p : LocalList m × Seed => (policy p.1 p.2).val))
    (hT : UniformReserveRule ν policy r) (e : Equiv.Perm (Fin m))
    (L : LocalList m) (S : Finset (Fin m)) :
    (positiveLaw ν policy hp (L ∘ e.symm)).mass (e.finsetCongr S) =
      (positiveLaw ν policy hp L).mass S := by
  classical
  simp only [positiveLaw, FiniteLaw.ofMeasure_mass, hT.positive_law,
    topChoices_relabel, Finset.card_map, Finset.mem_map_equiv,
    Equiv.symm_apply_apply]

def localPositiveStatistic {D : Type*} (ν : Measure Seed) (policy : LocalPolicy m c Seed)
    (entry : D → Option ℝ) (weight : D → ℝ) (d : Fin m → D) (i : Fin m) : ℝ :=
  ∫ s, if i ∈ positiveSelection (fun l => entry (d l))
    (policy (fun l => entry (d l)) s).val then weight (d i) else 0 ∂ν

theorem localPositiveStatistic_relabel {D : Type*}
    (ν : Measure Seed) [IsProbabilityMeasure ν] (policy : LocalPolicy m c Seed)
    (hp : Measurable (fun p : LocalList m × Seed => (policy p.1 p.2).val))
    (hT : UniformReserveRule ν policy r) (entry : D → Option ℝ) (weight : D → ℝ)
    (e : Equiv.Perm (Fin m)) (d : Fin m → D) (i : Fin m) :
    localPositiveStatistic ν policy entry weight (d ∘ e.symm) (e i) =
      localPositiveStatistic ν policy entry weight d i := by
  classical
  let L : LocalList m := fun l => entry (d l)
  unfold localPositiveStatistic
  simp only [Function.comp_apply, Equiv.symm_apply_apply]
  change (∫ s, if e i ∈ positiveSelection (L ∘ e.symm)
      (policy (L ∘ e.symm) s).val then weight (d i) else 0 ∂ν) =
    ∫ s, if i ∈ positiveSelection L (policy L s).val then weight (d i) else 0 ∂ν
  have hsel (L' : LocalList m) : Measurable
      (fun s => positiveSelection L' (policy L' s).val) :=
    (measurable_positiveSelection_policy policy hp).comp
      (measurable_const.prodMk measurable_id)
  rw [← FiniteLaw.expect_ofMeasure ν
      (fun s => positiveSelection (L ∘ e.symm) (policy (L ∘ e.symm) s).val)
      (hsel _) (fun S => if e i ∈ S then weight (d i) else 0),
    ← FiniteLaw.expect_ofMeasure ν (fun s => positiveSelection L (policy L s).val)
      (hsel _) (fun S => if i ∈ S then weight (d i) else 0)]
  change (positiveLaw ν policy hp (L ∘ e.symm)).expect
      (fun S => if e i ∈ S then weight (d i) else 0) =
    (positiveLaw ν policy hp L).expect (fun S => if i ∈ S then weight (d i) else 0)
  unfold FiniteLaw.expect
  rw [← Equiv.sum_comp e.finsetCongr]
  apply Finset.sum_congr rfl
  intro S _
  simp only [Equiv.finsetCongr_apply, Finset.mem_map_equiv, Equiv.symm_apply_apply]
  have hm : (positiveLaw ν policy hp (L ∘ e.symm)).mass (S.map e.toEmbedding) =
      (positiveLaw ν policy hp L).mass S := positiveLaw_mass_relabel ν policy hp hT e L S
  rw [hm]

theorem measurable_localPositiveStatistic {D : Type*} [MeasurableSpace D]
    (ν : Measure Seed) [SFinite ν] (policy : LocalPolicy m c Seed)
    (hp : Measurable (fun p : LocalList m × Seed => (policy p.1 p.2).val))
    (entry : D → Option ℝ) (hentry : Measurable entry)
    (weight : D → ℝ) (hweight : Measurable weight) (i : Fin m) :
    Measurable (fun d => localPositiveStatistic ν policy entry weight d i) := by
  classical
  have hL : Measurable (fun p : (Fin m → D) × Seed => fun l => entry (p.1 l)) :=
    measurable_pi_lambda _ fun l => hentry.comp ((measurable_pi_apply l).comp measurable_fst)
  have hS := (measurable_positiveSelection_policy policy hp).comp (hL.prodMk measurable_snd)
  have hf : Measurable (fun p : (Fin m → D) × Seed =>
      if i ∈ positiveSelection (fun l => entry (p.1 l))
        (policy (fun l => entry (p.1 l)) p.2).val then weight (p.1 i) else 0) :=
    Measurable.ite (hS (MeasurableSet.of_discrete : MeasurableSet {T : Finset (Fin m) | i ∈ T}))
      (hweight.comp ((measurable_pi_apply i).comp measurable_fst)) measurable_const
  exact hf.stronglyMeasurable.integral_prod_right'.measurable

end FCAppendix.CommonReserve
