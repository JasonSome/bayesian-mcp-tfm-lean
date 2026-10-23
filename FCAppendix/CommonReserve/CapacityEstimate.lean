import FCAppendix.CommonReserve.FiniteEstimates
import FCAppendix.CommonReserve.ZeroTies

noncomputable section
namespace FCAppendix.CommonReserve
open Game MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators
variable {m n c : ℕ} {r : ℝ} {Seed : Type*} [MeasurableSpace Seed]

def positiveLoad (Γ : FiniteGame m n c r Seed) : ℝ :=
  (∑ j, ∫ ω, ((positivePlayedAllocation Γ j ω).card : ℝ) ∂Γ.sampleLaw) / m

theorem topChoice_unused_le_above_reserve (L : LocalList m)
    (S : Finset (Fin m)) (hS : TopChoice L r c S) (hr : 0 ≤ r) :
    (c : ℝ) - S.card ≤
      max ((c : ℝ) - (Finset.univ.filter
        (fun i => L i ≠ none ∧ r < Bayes.entryBid (L i))).card) 0 := by
  classical
  have hsub : (Finset.univ.filter
      (fun i => L i ≠ none ∧ r < Bayes.entryBid (L i))) ⊆ positiveEligible L r := by
    intro i hi
    have hh := (Finset.mem_filter.mp hi).2
    exact (mem_positiveEligible_iff L r i).mpr ⟨hh.1, hh.2.le, hr.trans_lt hh.2⟩
  rw [hS.card_eq_min]
  by_cases hc : c ≤ (positiveEligible L r).card
  · rw [Nat.min_eq_left hc, sub_self]
    exact le_max_right _ _
  · rw [Nat.min_eq_right (le_of_not_ge hc)]
    have hh : ((Finset.univ.filter
        (fun i => L i ≠ none ∧ r < Bayes.entryBid (L i))).card : ℝ) ≤
        (positiveEligible L r).card := Nat.cast_le.mpr (Finset.card_le_card hsub)
    exact (sub_le_sub_left hh (c : ℝ)).trans (le_max_left _ _)

theorem ae_positive_capacity_shortfall (Γ : FiniteGame m n c r Seed) (j : Fin n)
    (hT : UniformReserveRule Γ.seedLaw (Γ.policy j) r) :
    ∀ᵐ ω ∂Γ.sampleLaw, (c : ℝ) - (positivePlayedAllocation Γ j ω).card ≤
      slotShortfall (c := c) j r ω.1 := by
  classical
  have hm : Measurable (fun ω : Sample m n r Seed =>
      (c : ℝ) - (positivePlayedAllocation Γ j ω).card) :=
    measurable_const.sub ((measurable_of_countable
      (fun S : Finset (Fin m) => (S.card : ℝ))).comp
        (measurable_positivePlayedAllocation Γ j))
  have hset : MeasurableSet {ω : Sample m n r Seed |
      (c : ℝ) - (positivePlayedAllocation Γ j ω).card ≤
        slotShortfall (c := c) j r ω.1} :=
    measurableSet_le hm ((measurable_slotShortfall j r).comp measurable_fst)
  apply (Measure.ae_prod_iff_ae_ae hset).mpr
  apply Eventually.of_forall
  intro d
  let L : LocalList m := fun i => (d i).2.val j
  have hs : ∀ᵐ s ∂(Measure.pi fun _ : Fin n => Γ.seedLaw),
      TopChoice L r c (positiveSelection L (Γ.policy j L (s j)).val) :=
    (measurePreserving_eval (fun _ : Fin n => Γ.seedLaw) j).quasiMeasurePreserving.ae
      (hT.ae_topChoice L)
  filter_upwards [hs] with s hs
  have hb := topChoice_unused_le_above_reserve L
    (positiveSelection L (Γ.policy j L (s j)).val) hs Γ.reserve_nonneg
  have hL : CommonReserve.observe (playedProfile (d, s)) j = L := rfl
  have hA : positivePlayedAllocation Γ j (d, s) =
      positiveSelection L (Γ.policy j L (s j)).val := by
    unfold positivePlayedAllocation playedAllocation CommonReserve.allocation
    rw [hL]
  rw [hA]
  simpa only [slotShortfall, PiBinomial.count, aboveAt, Set.mem_setOf_eq, L] using hb

theorem integral_positive_capacity_lower (Γ : FiniteGame m n c r Seed) (hm : 0 < m)
    (j : Fin n) (hT : UniformReserveRule Γ.seedLaw (Γ.policy j) r)
    (δ : ℝ) (hδ : 0 ≤ δ) (hPr : r < price Γ δ) :
    (c : ℝ) / m - (δ + 1 / (2 * Real.sqrt m)) ≤
      (∫ ω, ((positivePlayedAllocation Γ j ω).card : ℝ) ∂Γ.sampleLaw) / m := by
  have hi := (integrable_const (c : ℝ)).sub (integrable_positivePlayedAllocation_card Γ j)
  have hh := integral_mono_ae hi (integrable_slotShortfall_sample Γ j r)
    (ae_positive_capacity_shortfall Γ j hT)
  simp only [Pi.sub_apply] at hh
  rw [integral_sub (integrable_const _) (integrable_positivePlayedAllocation_card Γ j),
    integral_const, probReal_univ, one_smul] at hh
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hh' := div_le_div_of_nonneg_right hh hmR.le
  have he : (∫ ω : Sample m n r Seed, slotShortfall (c := c) j r ω.1 ∂Γ.sampleLaw) =
      ∫ d, slotShortfall (c := c) j r d ∂(Measure.pi fun _ : Fin m => Γ.userLaw) := by
    simp only [FiniteGame.sampleLaw, integral_fun_fst, probReal_univ, one_smul]
  rw [he] at hh'
  have ht := PiBinomial.integral_normalized_shortfall_le Γ.userLaw (aboveAt j r)
    (measurableSet_aboveAt j r) (Finset.univ : Finset (Fin m)) (by simpa using hm)
    ((c : ℝ) / m) ((c : ℝ) / m) δ hδ (price_tail_below Γ δ r le_rfl hPr j).le
  simp only [Finset.card_univ, Fintype.card_fin, sub_self, abs_zero, add_zero,
    mul_div_cancel₀ _ hmR.ne'] at ht
  have he' := hh'.trans ht
  rw [sub_div] at he'
  linarith

theorem positiveLoad_lower_of_price_gt_reserve (Γ : FiniteGame m n c r Seed)
    (hm : 0 < m) (δ : ℝ) (hδ : 0 ≤ δ) (hPr : r < price Γ δ)
    (hT : ∀ j, UniformReserveRule Γ.seedLaw (Γ.policy j) r) :
    (n : ℝ) * ((c : ℝ) / m) - (n : ℝ) * (δ + 1 / (2 * Real.sqrt m)) ≤
      positiveLoad Γ := by
  have hh := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) =>
    integral_positive_capacity_lower Γ hm j (hT j) δ hδ hPr
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    ← Finset.sum_div] at hh
  dsimp only [positiveLoad]
  linarith

end FCAppendix.CommonReserve
