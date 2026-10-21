import FCAppendix.Affine.UniformFinite.SeedPayoffRejection

noncomputable section
namespace FCAppendix.Affine.UniformFinite
open Set MeasureTheory ProbabilityTheory Filter Topology Classical
open scoped BigOperators
open Uniform05

namespace Literal

theorem ramp_monotone : Monotone ramp := by
  intro x y hxy
  exact max_le_max le_rfl (min_le_min le_rfl hxy)

theorem guardWeight_monotone {κ : Type*} [Fintype κ]
    {outer inner : ℝ} (hgap : outer < inner) {s s' : κ → ℝ}
    (h : ∀ k, s k ≤ s' k) : guardWeight outer inner s ≤ guardWeight outer inner s' := by
  unfold guardWeight
  apply Finset.prod_le_prod
  · intro k _
    exact (ramp_bounds _).1
  · intro k _
    apply ramp_monotone
    exact div_le_div_of_nonneg_right (sub_le_sub_right (h k) outer) (sub_pos.mpr hgap).le

end Literal

namespace Source

def lowPrefixTop (i : Row) (G : RestrictedLaw i) : ℝ :=
  min (cap i) (min (rootHi i G) (min G.rejectionRoot (G.multiplier + 3*guardRadius i)))

theorem lowPrefixTop_bounds (i : Row) (G : RestrictedLaw i) :
    lowPrefixTop i G ≤ cap i ∧ lowPrefixTop i G ≤ rootHi i G ∧
      lowPrefixTop i G ≤ G.rejectionRoot ∧
      lowPrefixTop i G ≤ G.multiplier + 3*guardRadius i := by
  unfold lowPrefixTop
  exact ⟨min_le_left _ _,(min_le_right _ _).trans (min_le_left _ _),
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)),
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))⟩

theorem lowPrefixTop_pos (i : Row) (G : RestrictedLaw i) : 0 < lowPrefixTop i G := by
  have hm : 0 < G.multiplier := (demandLo_pos i).trans G.multiplier_guards.1
  have hr : 0 < G.rejectionRoot := (rejectionLo_pos i).trans G.rejectionRoot_guards.1
  have hhi : 0 < rootHi i G := (rootBounds i G).1.trans (rootBounds i G).2.1
  unfold lowPrefixTop
  exact lt_min (cap_pos i) (lt_min hhi (lt_min hr (by linarith [guardRadius_pos i])))

theorem lawWeight_zero_on_prefix (i : Row) (G : RestrictedLaw i) {b : ℝ}
    (hb : b ≤ lowPrefixTop i G) : lawWeight i G b = 0 := by
  have hp := lowPrefixTop_bounds i G
  apply le_antisymm _ (lawWeight_range i G b).1
  by_contra hnot
  have hpos : 0 < lawWeight i G b := lt_of_not_ge hnot
  exact not_lt_of_ge (hb.trans hp.2.2.2)
    (positive_weight_eligibility i G (hb.trans hp.1) hpos)

variable {M : ℕ}

theorem lowDemand_update_mono (i : Row) (G : RestrictedLaw i) (row : CountRow M)
    (b : Fin M → ℝ) (a : Fin M) (ha : a ∈ row.lower) {x y : ℝ} (hxy : x ≤ y) :
    lowDemand i G row (Function.update b a x) ≤ lowDemand i G row (Function.update b a y) := by
  apply Finset.sum_le_sum
  intro j _
  by_cases hja : j=a
  · subst j
    simp only [lowerBids_of_mem row _ ha,Function.update_self]
    exact exposure_monotone_bid (xi_range i).1 (rootBounds i G).1 hxy
  · simp only [lowerBids,Function.update_of_ne hja]
    exact le_rfl

theorem highDemand_update_eq_on_prefix (i : Row) (G : RestrictedLaw i) (row : CountRow M)
    (b : Fin M → ℝ) (a : Fin M) (ha : a ∈ row.lower) {x y : ℝ}
    (hx : x ≤ lowPrefixTop i G) (hy : y ≤ lowPrefixTop i G) :
    highDemand i G row (Function.update b a x) = highDemand i G row (Function.update b a y) := by
  apply Finset.sum_congr rfl
  intro j _
  by_cases hja : j=a
  · subst j
    simp only [lowerBids_of_mem row _ ha,Function.update_self,
      exposure_zero (hx.trans (lowPrefixTop_bounds i G).2.1),
      exposure_zero (hy.trans (lowPrefixTop_bounds i G).2.1)]
  · simp only [lowerBids,Function.update_of_ne hja]

theorem sourceWeights_update_eq_on_prefix (i : Row) (G : RestrictedLaw i)
    (row : CountRow M) (b : Fin M → ℝ) (a : Fin M) {x y : ℝ}
    (hx : x ≤ lowPrefixTop i G) (hy : y ≤ lowPrefixTop i G) :
    sourceWeights i G row (Function.update b a x) = sourceWeights i G row (Function.update b a y) := by
  apply Subtype.ext
  funext j
  by_cases hja : j=a
  · subst j
    simp [sourceWeights,lawWeight_zero_on_prefix i G hx,lawWeight_zero_on_prefix i G hy]
  · simp [sourceWeights,Function.update_of_ne hja]

theorem rejectionSum_update_eq_on_prefix (i : Row) (G : RestrictedLaw i)
    (row : CountRow M) (b : Fin M → ℝ) (a : Fin M) (ha : a ∈ row.lower) {x y : ℝ}
    (hx : x ≤ lowPrefixTop i G) (hy : y ≤ lowPrefixTop i G) :
    rejectionSum i G row (Function.update b a x) = rejectionSum i G row (Function.update b a y) := by
  apply Finset.sum_congr rfl
  intro j _
  by_cases hja : j=a
  · subst j
    simp only [lowerBids_of_mem row _ ha,Function.update_self,
      rejectionExposure_zero (hx.trans (lowPrefixTop_bounds i G).2.2.1),
      rejectionExposure_zero (hy.trans (lowPrefixTop_bounds i G).2.2.1)]
  · simp only [lowerBids,Function.update_of_ne hja]

theorem other_slacks_update_eq_on_prefix (i : Row) (G : RestrictedLaw i)
    (row : CountRow M) (b : Fin M → ℝ) (a : Fin M) (ha : a ∈ row.lower) {x y : ℝ}
    (hx : x ≤ lowPrefixTop i G) (hy : y ≤ lowPrefixTop i G) (k : Fin 7) (hk : k≠0) :
    sourceSlacks i G row (Function.update b a x) k =
      sourceSlacks i G row (Function.update b a y) k := by
  have hh := highDemand_update_eq_on_prefix i G row b a ha hx hy
  have hw := sourceWeights_update_eq_on_prefix i G row b a hx hy
  have hr := rejectionSum_update_eq_on_prefix i G row b a ha hx hy
  fin_cases k <;> simp_all [sourceSlacks]

theorem rawAlpha_update_mono_on_prefix (i : Row) (G : RestrictedLaw i)
    (row : CountRow M) (b : Fin M → ℝ) (a : Fin M) (ha : a ∈ row.lower) {x y : ℝ}
    (hxy : x ≤ y) (hy : y ≤ lowPrefixTop i G) :
    rawAlpha i G row (Function.update b a x) ≤ rawAlpha i G row (Function.update b a y) := by
  apply Literal.guardWeight_monotone (by linarith [common_guard_margin i])
  intro k
  by_cases hk : k=0
  · subst k
    simp only [sourceSlacks,Matrix.cons_val_zero]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg M)
    linarith [lowDemand_update_mono i G row b a ha hxy]
  · exact (other_slacks_update_eq_on_prefix i G row b a ha (hxy.trans hy) hy k hk).le

theorem seedCount_update_eq_above_seed (i : Row) (row : CountRow M)
    (b : Fin M → ℝ) (a : Fin M) {x y : ℝ} (hx : t i/2 < x) (hy : t i/2 < y) :
    seedCount i row (Function.update b a x) = seedCount i row (Function.update b a y) := by
  unfold seedCount
  congr 1
  apply Finset.filter_congr
  intro j _
  by_cases hja : j=a
  · subst j
    simp [not_le.mpr hx,not_le.mpr hy]
  · simp [Function.update_of_ne hja]

theorem guardAlpha_update_mono_on_prefix (i : Row) (G : RestrictedLaw i)
    (row : CountRow M) (b : Fin M → ℝ) (a : Fin M) (ha : a ∈ row.lower) {x y : ℝ}
    (hx : t i/2 < x) (hxy : x ≤ y) (hy : y ≤ lowPrefixTop i G) :
    guardAlpha i G row (Function.update b a x) ≤ guardAlpha i G row (Function.update b a y) := by
  have hs := seedCount_update_eq_above_seed i row b a hx (hx.trans_le hxy)
  unfold guardAlpha
  rw [hs]
  split_ifs
  · exact le_rfl
  · exact rawAlpha_update_mono_on_prefix i G row b a ha hxy hy

theorem focal_weight_zero_on_prefix (i : Row) (G : RestrictedLaw i) (row : CountRow M)
    (b : Fin M → ℝ) (a : Fin M) (ha : a ∈ row.lower) (hb : b a ≤ lowPrefixTop i G) :
    (sourceWeights i G row b).1 a = 0 := by
  simp only [sourceWeights,if_pos ha,lawWeight_zero_on_prefix i G hb]

variable [NeZero M]

theorem focal_omitted_from_weighted_path_on_prefix (i : Row) (G : RestrictedLaw i)
    (row : CountRow M) (b : Fin M → ℝ) (a : Fin M) (ha : a ∈ row.lower)
    (hb : b a ≤ lowPrefixTop i G)
    (hW : (imbalance row : ℝ) < WeightedSampling.totalWeight (sourceWeights i G row b))
    (p : WeightedSampling.Path (Fin M) (imbalance row))
    (hp : 0 < (WeightedSampling.pathLaw (sourceWeights i G row b) (imbalance row) ∅).mass p) :
    a ∉ WeightedSampling.finalSet (imbalance row) ∅ p := by
  intro hin
  have h := WeightedSampling.finalSet_weight_pos (sourceWeights i G row b) (imbalance row) ∅
    (by simpa using hW) (by simp) p hp a hin
  rw [focal_weight_zero_on_prefix i G row b a ha hb] at h
  exact (lt_irrefl 0) h

theorem pure_rejects_on_prefix (i : Row) (G : RestrictedLaw i) (row : CountRow M)
    (b : Fin M → ℝ) (hb0 : ∀ j, 0 ≤ b j) (a : Fin M) (ha : a ∈ row.lower)
    (hb : b a ≤ lowPrefixTop i G) (hα : 0 < rawAlpha i G row b) :
    a ∉ ((lowerTemplate row).selection (kappa i) (lowerBids row b)).1 ∧
      a ∉ ((lowerTemplate row).selection (kappa i) (lowerBids row b)).2 := by
  apply SeedRejection.pure_selection_rejects (lowerTemplate row) (kappa_range i).2.le
    (lowerBids row b)
  · intro j
    by_cases hj : j ∈ row.lower
    · simpa [lowerBids,hj] using hb0 j
    · simp [lowerBids,hj]
  · exact SeedRejection.raw_guard_high_count i G row b hα
  · simpa only [lowerBids_of_mem row _ ha] using hb.trans (lowPrefixTop_bounds i G).2.2.1

end Source
end FCAppendix.Affine.UniformFinite
