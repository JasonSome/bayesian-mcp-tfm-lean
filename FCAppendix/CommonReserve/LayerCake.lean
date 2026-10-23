import FCAppendix.CommonReserve.FiniteEstimates

noncomputable section
namespace FCAppendix.CommonReserve
open Game MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators
variable {m n c : ℕ} {r : ℝ} {Seed : Type*} [MeasurableSpace Seed]

def localError (Γ : FiniteGame m n c r Seed) (j : Fin n) (p : ℝ)
    (ω : Sample m n r Seed) : ℝ :=
  ∑ i ∈ playedAllocation Γ j ω, max (p - Bayes.entryBid ((ω.1 i).2.val j)) 0

theorem localError_eq_sum (Γ : FiniteGame m n c r Seed) (j : Fin n)
    (p : ℝ) (ω : Sample m n r Seed) : localError Γ j p ω =
      ∑ i, if i ∈ playedAllocation Γ j ω then
        max (p - Bayes.entryBid ((ω.1 i).2.val j)) 0 else 0 := by
  classical
  rw [← Finset.sum_filter]
  simp [localError]

theorem measurable_localError (Γ : FiniteGame m n c r Seed) (j : Fin n) (p : ℝ) :
    Measurable (localError Γ j p) := by
  classical
  change Measurable (fun ω : Sample m n r Seed => localError Γ j p ω)
  simp_rw [localError_eq_sum]
  apply Finset.measurable_sum
  intro i _
  apply Measurable.ite
    ((measurable_playedAllocation Γ j)
      (MeasurableSet.of_discrete : MeasurableSet {S : Finset (Fin m) | i ∈ S}))
    _ measurable_const
  exact (measurable_const.sub ((measurable_coordinateBid j).comp
    ((measurable_pi_apply i).comp measurable_fst))).max measurable_const

theorem localError_nonneg (Γ : FiniteGame m n c r Seed) (j : Fin n)
    (p : ℝ) (ω : Sample m n r Seed) : 0 ≤ localError Γ j p ω :=
  Finset.sum_nonneg fun _ _ => le_max_right _ _

theorem localError_le (Γ : FiniteGame m n c r Seed) (j : Fin n)
    (p : ℝ) (ω : Sample m n r Seed) : localError Γ j p ω ≤ max p 0 * c := by
  calc
    _ ≤ ∑ _i ∈ playedAllocation Γ j ω, max p 0 :=
      Finset.sum_le_sum fun i _ => max_le_max (sub_le_self _ (played_bid_nonneg Γ j ω i)) le_rfl
    _ = (playedAllocation Γ j ω).card * max p 0 := by simp
    _ ≤ _ := by
      have hc : ((playedAllocation Γ j ω).card : ℝ) ≤ c :=
        Nat.cast_le.mpr (playedAllocation_card_le Γ j ω)
      nlinarith [mul_le_mul_of_nonneg_right hc (le_max_right p 0)]

theorem integrable_localError (Γ : FiniteGame m n c r Seed) (j : Fin n) (p : ℝ) :
    Integrable (localError Γ j p) Γ.sampleLaw := by
  apply Integrable.of_bound (measurable_localError Γ j p).aestronglyMeasurable (max p 0 * c)
  exact Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (localError_nonneg Γ j p ω)]
    exact localError_le Γ j p ω

theorem gap_layerCake (p b : ℝ) (hb : 0 ≤ b) :
    (∫ x in Ioc 0 p, if b < x then (1 : ℝ) else 0) = max (p - b) 0 := by
  have he : Ioi b ∩ Ioc 0 p = Ioc b p := by
    ext x
    simp only [mem_inter_iff, mem_Ioi, mem_Ioc]
    constructor
    · exact fun h => ⟨h.1, h.2.2⟩
    · exact fun h => ⟨h.1, hb.trans_lt h.1, h.2⟩
  change (∫ x in Ioc 0 p, (Ioi b).indicator (fun _ => (1 : ℝ)) x) = _
  rw [integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi, he]
  simp only [setIntegral_const, smul_eq_mul, mul_one, Real.volume_real_Ioc]

theorem localError_eq_layerCake (Γ : FiniteGame m n c r Seed) (j : Fin n)
    (p : ℝ) (ω : Sample m n r Seed) :
    localError Γ j p ω = ∫ x in Ioc 0 p, lowCount Γ j x ω := by
  classical
  haveI : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) p)) :=
    ⟨by simp⟩
  have hi (i : Fin m) : Integrable
      (fun x : ℝ => if i ∈ playedAllocation Γ j ω ∧ Bayes.entryBid ((ω.1 i).2.val j) < x
        then (1 : ℝ) else 0) (volume.restrict (Ioc 0 p)) := by
    have hm : MeasurableSet {x : ℝ | i ∈ playedAllocation Γ j ω ∧
        Bayes.entryBid ((ω.1 i).2.val j) < x} := by
      by_cases hs : i ∈ playedAllocation Γ j ω
      · simpa only [hs, true_and] using
          (measurableSet_lt measurable_const measurable_id :
            MeasurableSet {x : ℝ | Bayes.entryBid ((ω.1 i).2.val j) < x})
      · simp only [hs, false_and, Set.setOf_false, MeasurableSet.empty]
    apply Integrable.of_bound
      (Measurable.ite hm measurable_const measurable_const).aestronglyMeasurable 1
    exact Eventually.of_forall fun x => by split_ifs <;> norm_num
  simp_rw [lowCount_eq_sum]
  rw [integral_finsetSum _ (fun i _ => hi i), localError_eq_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hs : i ∈ playedAllocation Γ j ω
  · simp only [hs, true_and, if_true]
    exact (gap_layerCake p _ (played_bid_nonneg Γ j ω i)).symm
  · simp [hs]

theorem integrable_layerCake (Γ : FiniteGame m n c r Seed) (j : Fin n) (p : ℝ) :
    Integrable (fun z : ℝ × Sample m n r Seed => lowCount Γ j z.1 z.2)
      ((volume.restrict (Ioc 0 p)).prod Γ.sampleLaw) := by
  haveI : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) p)) :=
    ⟨by simp⟩
  apply Integrable.of_bound (measurable_lowCount_joint Γ j).aestronglyMeasurable (c : ℝ)
  exact Eventually.of_forall fun z => by
    rw [Real.norm_eq_abs, abs_of_nonneg (lowCount_nonneg Γ j z.1 z.2)]
    exact lowCount_le Γ j z.1 z.2

theorem integral_localError_eq_layerCake (Γ : FiniteGame m n c r Seed)
    (j : Fin n) (p : ℝ) :
    (∫ ω, localError Γ j p ω ∂Γ.sampleLaw) =
      ∫ x in Ioc 0 p, ∫ ω, lowCount Γ j x ω ∂Γ.sampleLaw := by
  simp_rw [localError_eq_layerCake]
  exact (integral_integral_swap (integrable_layerCake Γ j p)).symm

theorem lowCount_eq_zero_of_le_reserve (Γ : FiniteGame m n c r Seed)
    (j : Fin n) (x : ℝ) (hx : x ≤ r) (ω : Sample m n r Seed) :
    lowCount Γ j x ω = 0 := by
  classical
  rw [lowCount_eq_sum]
  apply Finset.sum_eq_zero
  intro i _
  rw [if_neg]
  rintro ⟨hi, hlt⟩
  exact (not_lt_of_ge (hx.trans (played_bid_ge_reserve Γ j ω i hi))) hlt

theorem integral_localError_normalized_le (Γ : FiniteGame m n c r Seed)
    (hm : 0 < m) (hn : 0 < n) (j : Fin n)
    (hT : UniformReserveRule Γ.seedLaw (Γ.policy j) r)
    (δ : ℝ) (hδ : 0 ≤ δ) (hδκ : δ < (c : ℝ) / m) :
    (∫ ω, localError Γ j (price Γ δ) ω ∂Γ.sampleLaw) / m ≤
      price Γ δ * (δ + 1 / (2 * Real.sqrt m)) := by
  let p := price Γ δ
  let η := δ + 1 / (2 * Real.sqrt m)
  have hp : 0 ≤ p := price_nonneg Γ δ hn hδκ
  have hη : 0 ≤ η := add_nonneg hδ (by positivity)
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  haveI : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) p)) :=
    ⟨by simp⟩
  have hb : ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) p),
      (∫ ω, lowCount Γ j x ω ∂Γ.sampleLaw) ≤ (m : ℝ) * η := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
      (volume.restrict (Ioc (0 : ℝ) p)).ae_ne p] with x hx hxp
    have hxp' : x < p := lt_of_le_of_ne hx.2 hxp
    by_cases hxr : x ≤ r
    · simp_rw [lowCount_eq_zero_of_le_reserve Γ j x hxr, integral_zero]
      exact mul_nonneg hmR.le hη
    · have ht := (price_tail_below Γ δ x (le_of_not_ge hxr) hxp' j).le
      have hh := integral_lowCount_normalized_le Γ hm j hT δ x hδ ht
      exact (div_le_iff₀ hmR).mp hh |>.trans_eq (mul_comm η (m : ℝ))
  have hh := integral_mono_ae (integrable_layerCake Γ j p).integral_prod_left
    (integrable_const ((m : ℝ) * η)) hb
  rw [← integral_localError_eq_layerCake] at hh
  simp only [setIntegral_const, smul_eq_mul, Real.volume_real_Ioc, sub_zero,
    max_eq_left hp] at hh
  apply (div_le_iff₀ hmR).mpr
  nlinarith [hh]

end FCAppendix.CommonReserve
