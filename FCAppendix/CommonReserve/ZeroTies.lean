import FCAppendix.CommonReserve.SourceStatistics

noncomputable section
namespace FCAppendix.CommonReserve
open Game MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators

variable {m c : ℕ} {r : ℝ} {Seed : Type*} [MeasurableSpace Seed]

theorem TopChoice.card_eq_min {L : LocalList m} {S : Finset (Fin m)}
    (h : TopChoice L r c S) : S.card = min c (positiveEligible L r).card := by
  classical
  apply le_antisymm (le_min h.2.1 (Finset.card_le_card h.1))
  by_contra hn
  have hlt : S.card < min c (positiveEligible L r).card := lt_of_not_ge hn
  obtain ⟨i, hi, hni⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (hlt.trans_le (min_le_right _ _))
  have hp : 0 < Bayes.entryBid (positiveList L r i) := by
    rw [positiveList_entry_of_mem L r i hi]
    exact ((mem_positiveEligible_iff L r i).mp hi).2.2
  have he := Finite.optimal_fills c _ S h.2 i hni hp
  omega

def zeroSelection (L : LocalList m) (S : Finset (Fin m)) : Finset (Fin m) := by
  classical
  exact S.filter (fun i => L i = some 0)

def zeroEligible (L : LocalList m) : Finset (Fin m) := by
  classical
  exact Finset.univ.filter (fun i => L i = some 0)

def zeroSlots (L : LocalList m) (r : ℝ) (c : ℕ) : ℝ :=
  max ((c : ℝ) - (positiveEligible L r).card) 0

theorem zeroSlots_nonneg (L : LocalList m) : 0 ≤ zeroSlots L r c := le_max_right _ _

theorem zeroSlots_le (L : LocalList m) : zeroSlots L r c ≤ c := by
  unfold zeroSlots
  exact max_le (sub_le_self _ (Nat.cast_nonneg _)) (Nat.cast_nonneg _)

theorem zeroSelection_card_le {L : LocalList m} {S : Finset (Fin m)}
    (hc : S.card ≤ c) (hS : TopChoice L r c (positiveSelection L S)) :
    ((zeroSelection L S).card : ℝ) ≤ zeroSlots L r c := by
  classical
  have hd : Disjoint (positiveSelection L S) (zeroSelection L S) := by
    apply Finset.disjoint_left.mpr
    intro i hi hz
    have hp := (Finset.mem_filter.mp hi).2
    have he := (Finset.mem_filter.mp hz).2
    simp only [he, Bayes.entryBid] at hp
    exact (lt_irrefl 0) hp
  have hs : positiveSelection L S ∪ zeroSelection L S ⊆ S := by
    intro i hi
    rcases Finset.mem_union.mp hi with hi | hi
    · exact (Finset.mem_filter.mp hi).1
    · exact (Finset.mem_filter.mp hi).1
  have hb := (Finset.card_le_card hs).trans hc
  rw [Finset.card_union_of_disjoint hd, hS.card_eq_min] at hb
  unfold zeroSlots
  by_cases hN : c ≤ (positiveEligible L r).card
  · rw [Nat.min_eq_left hN] at hb
    have hz : (zeroSelection L S).card = 0 := by omega
    simp only [hz, Nat.cast_zero]
    exact le_max_right _ _
  · have hN' : (positiveEligible L r).card ≤ c := by omega
    rw [Nat.min_eq_right hN'] at hb
    have hbR : ((positiveEligible L r).card : ℝ) + (zeroSelection L S).card ≤ c := by
      exact_mod_cast hb
    exact (by linarith : ((zeroSelection L S).card : ℝ) ≤
      (c : ℝ) - (positiveEligible L r).card).trans (le_max_left _ _)

theorem measurable_policy_membership (policy : LocalPolicy m c Seed)
    (hp : Measurable (fun p : LocalList m × Seed => (policy p.1 p.2).val))
    (L : LocalList m) (i : Fin m) :
    MeasurableSet {s | i ∈ (policy L s).val} :=
  (hp.comp (measurable_const.prodMk measurable_id))
    (MeasurableSet.of_discrete : MeasurableSet {S : Finset (Fin m) | i ∈ S})

theorem integral_policy_membership (ν : Measure Seed) [IsProbabilityMeasure ν]
    (policy : LocalPolicy m c Seed)
    (hp : Measurable (fun p : LocalList m × Seed => (policy p.1 p.2).val))
    (L : LocalList m) (i : Fin m) :
    (∫ s, if i ∈ (policy L s).val then (1 : ℝ) else 0 ∂ν) =
      ν.real {s | i ∈ (policy L s).val} := by
  simpa only [Set.indicator, Set.mem_setOf_eq, Pi.one_apply] using
    (integral_indicator_one (μ := ν) (measurable_policy_membership policy hp L i))

theorem integrable_policy_membership (ν : Measure Seed) [IsProbabilityMeasure ν]
    (policy : LocalPolicy m c Seed)
    (hp : Measurable (fun p : LocalList m × Seed => (policy p.1 p.2).val))
    (L : LocalList m) (i : Fin m) :
    Integrable (fun s => if i ∈ (policy L s).val then (1 : ℝ) else 0) ν := by
  exact Integrable.of_bound
    (Measurable.ite (measurable_policy_membership policy hp L i)
      measurable_const measurable_const).aestronglyMeasurable 1
    (Eventually.of_forall fun _ => by split <;> norm_num)

theorem zero_marginal_le_shortfall (ν : Measure Seed) [IsProbabilityMeasure ν]
    (policy : LocalPolicy m c Seed)
    (hp : Measurable (fun p : LocalList m × Seed => (policy p.1 p.2).val))
    (hT : UniformReserveRule ν policy r) (L : LocalList m) (i : Fin m)
    (hi : L i = some 0) :
    ν.real {s | i ∈ (policy L s).val} ≤
      zeroSlots L r c / (zeroEligible L).card := by
  classical
  have hZ : 0 < (zeroEligible L).card := Finset.card_pos.mpr ⟨i, by simp [zeroEligible, hi]⟩
  have hZR : (0 : ℝ) < (zeroEligible L).card := by exact_mod_cast hZ
  apply (le_div_iff₀ hZR).mpr
  have hpoint : ∀ᵐ s ∂ν,
      (∑ l ∈ zeroEligible L, if l ∈ (policy L s).val then (1 : ℝ) else 0) ≤
        zeroSlots L r c := by
    filter_upwards [hT.ae_topChoice L] with s hs
    have he : (∑ l ∈ zeroEligible L,
        if l ∈ (policy L s).val then (1 : ℝ) else 0) =
        ((zeroSelection L (policy L s).val).card : ℝ) := by
      have hz : zeroSelection L (policy L s).val =
          (zeroEligible L).filter (fun l => l ∈ (policy L s).val) := by
        ext l
        simp [zeroSelection, zeroEligible, and_comm]
      rw [hz]
      simp [Finset.filter_mem_eq_inter]
    rw [he]
    exact zeroSelection_card_le (policy L s).property.1 hs
  have hiSum : Integrable (fun s =>
      ∑ l ∈ zeroEligible L, if l ∈ (policy L s).val then (1 : ℝ) else 0) ν :=
    integrable_finsetSum _ fun l _ => integrable_policy_membership ν policy hp L l
  have hh := integral_mono_ae hiSum (integrable_const (zeroSlots L r c)) hpoint
  rw [integral_finsetSum _ (fun l _ => integrable_policy_membership ν policy hp L l),
    integral_const, probReal_univ, one_smul] at hh
  simp_rw [integral_policy_membership ν policy hp L] at hh
  have he : (∑ l ∈ zeroEligible L, ν.real {s | l ∈ (policy L s).val}) =
      ((zeroEligible L).card : ℝ) * ν.real {s | i ∈ (policy L s).val} := by
    calc
      _ = ∑ _l ∈ zeroEligible L, ν.real {s | i ∈ (policy L s).val} := by
        apply Finset.sum_congr rfl
        intro l hl
        exact hT.zero_marginal_eq L l i (Finset.mem_filter.mp hl).2 hi
      _ = _ := by simp
  rw [he] at hh
  simpa only [mul_comm] using hh

theorem positive_card_add_zeroSlots (L : LocalList m) :
    (min c (positiveEligible L r).card : ℝ) + zeroSlots L r c = c := by
  unfold zeroSlots
  by_cases hc : c ≤ (positiveEligible L r).card
  · have hcR : (c : ℝ) ≤ (positiveEligible L r).card := by exact_mod_cast hc
    rw [min_eq_left hcR, max_eq_right (sub_nonpos.mpr hcR), add_zero]
  · have hcN : (positiveEligible L r).card ≤ c := by omega
    have hcR : ((positiveEligible L r).card : ℝ) ≤ c := by exact_mod_cast hcN
    rw [min_eq_right hcR, max_eq_left (sub_nonneg.mpr hcR)]
    ring

end FCAppendix.CommonReserve
