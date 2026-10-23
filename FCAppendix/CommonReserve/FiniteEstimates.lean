import FCAppendix.CommonReserve.Quantiles
import FCAppendix.Finite.ReceiptShortfall

noncomputable section
namespace FCAppendix.CommonReserve
open Game MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Classical
variable {m n c : ℕ} {r : ℝ} {Seed : Type*} [MeasurableSpace Seed]

def playedProfile (ω : Sample m n r Seed) : Profile m n r := fun i => (ω.1 i).2

def playedAllocation (Γ : FiniteGame m n c r Seed) (j : Fin n)
    (ω : Sample m n r Seed) : Finset (Fin m) :=
  allocation (playedProfile ω) Γ.policy ω.2 j

theorem measurable_playedList (j : Fin n) :
    Measurable (fun ω : Sample m n r Seed => observe (playedProfile ω) j) := by
  apply measurable_pi_lambda
  intro i
  exact (measurable_coordinate j).comp ((measurable_pi_apply i).comp measurable_fst)

theorem measurable_playedAllocation (Γ : FiniteGame m n c r Seed) (j : Fin n) :
    Measurable (playedAllocation Γ j) :=
  (Γ.policy_measurable j).comp ((measurable_playedList j).prodMk
    ((measurable_pi_apply j).comp measurable_snd))

theorem playedAllocation_card_le (Γ : FiniteGame m n c r Seed) (j : Fin n)
    (ω : Sample m n r Seed) : (playedAllocation Γ j ω).card ≤ c :=
  (Γ.policy j (observe (playedProfile ω) j) (ω.2 j)).property.1

theorem played_bid_nonneg (Γ : FiniteGame m n c r Seed)
    (j : Fin n) (ω : Sample m n r Seed) (i : Fin m) :
    0 ≤ Bayes.entryBid ((ω.1 i).2.val j) := by
  cases he : (ω.1 i).2.val j with
  | none => simp [Bayes.entryBid]
  | some b => exact Γ.reserve_nonneg.trans ((ω.1 i).2.property j b he)

theorem played_bid_ge_reserve (Γ : FiniteGame m n c r Seed)
    (j : Fin n) (ω : Sample m n r Seed) (i : Fin m)
    (hi : i ∈ playedAllocation Γ j ω) : r ≤ Bayes.entryBid ((ω.1 i).2.val j) := by
  have hp := (Γ.policy j (observe (playedProfile ω) j) (ω.2 j)).property.2 i hi
  cases he : (ω.1 i).2.val j with
  | none => exact (hp he).elim
  | some b => exact (ω.1 i).2.property j b he

def positivePlayedAllocation (Γ : FiniteGame m n c r Seed) (j : Fin n)
    (ω : Sample m n r Seed) : Finset (Fin m) :=
  positiveSelection (observe (playedProfile ω) j) (playedAllocation Γ j ω)

theorem measurable_positivePlayedAllocation (Γ : FiniteGame m n c r Seed) (j : Fin n) :
    Measurable (positivePlayedAllocation Γ j) :=
  measurable_positiveSelection_joint.comp
    ((measurable_playedList j).prodMk (measurable_playedAllocation Γ j))

theorem positivePlayedAllocation_card_le (Γ : FiniteGame m n c r Seed)
    (j : Fin n) (ω : Sample m n r Seed) :
    (positivePlayedAllocation Γ j ω).card ≤ c :=
  (Finset.card_filter_le _ _).trans (playedAllocation_card_le Γ j ω)

theorem integrable_positivePlayedAllocation_card (Γ : FiniteGame m n c r Seed)
    (j : Fin n) :
    Integrable (fun ω => ((positivePlayedAllocation Γ j ω).card : ℝ)) Γ.sampleLaw := by
  apply Integrable.of_bound
    ((measurable_of_countable (fun S : Finset (Fin m) => (S.card : ℝ))).comp
      (measurable_positivePlayedAllocation Γ j)).aestronglyMeasurable (c : ℝ)
  exact Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
    change ((positivePlayedAllocation Γ j ω).card : ℝ) ≤ (c : ℝ)
    exact_mod_cast positivePlayedAllocation_card_le Γ j ω

theorem positiveEligible_actual_eq (_Γ : FiniteGame m n c r Seed)
    (j : Fin n) (d : Fin m → UserDraw n r) :
    positiveEligible (fun i => (d i).2.val j) r =
      Finset.univ.filter (fun i => d i ∈ aboveAt j 0) := by
  classical
  ext i
  simp only [mem_positiveEligible_iff, Finset.mem_filter, Finset.mem_univ,
    true_and, aboveAt, Set.mem_setOf_eq]
  constructor
  · exact fun h => ⟨h.1, h.2.2⟩
  · intro h
    refine ⟨h.1, ?_, h.2⟩
    cases he : (d i).2.val j with
    | none => exact (h.1 he).elim
    | some b => exact (d i).2.property j b he

def lowCount (Γ : FiniteGame m n c r Seed) (j : Fin n) (x : ℝ)
    (ω : Sample m n r Seed) : ℝ :=
  ((playedAllocation Γ j ω ∩ Finset.univ.filter
    (fun i => Bayes.entryBid ((ω.1 i).2.val j) < x)).card : ℝ)

theorem lowCount_eq_sum (Γ : FiniteGame m n c r Seed) (j : Fin n) (x : ℝ)
    (ω : Sample m n r Seed) : lowCount Γ j x ω =
      ∑ i, if i ∈ playedAllocation Γ j ω ∧ Bayes.entryBid ((ω.1 i).2.val j) < x
        then (1 : ℝ) else 0 := by
  classical
  simp only [lowCount, Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
  rw [← Finset.sum_filter]
  congr 1
  ext i
  simp

theorem measurable_lowCount_joint (Γ : FiniteGame m n c r Seed) (j : Fin n) :
    Measurable (fun p : ℝ × Sample m n r Seed => lowCount Γ j p.1 p.2) := by
  classical
  simp_rw [lowCount_eq_sum]
  apply Finset.measurable_sum
  intro i _
  apply Measurable.ite _ measurable_const measurable_const
  exact (((measurable_playedAllocation Γ j).comp measurable_snd)
    (MeasurableSet.of_discrete : MeasurableSet {S : Finset (Fin m) | i ∈ S})).inter
      (measurableSet_lt ((measurable_coordinateBid j).comp
        ((measurable_pi_apply i).comp (measurable_fst.comp measurable_snd))) measurable_fst)

theorem measurable_lowCount (Γ : FiniteGame m n c r Seed) (j : Fin n) (x : ℝ) :
    Measurable (lowCount Γ j x) :=
  Measurable.of_uncurry_left (f := lowCount Γ j) (x := x)
    (measurable_lowCount_joint Γ j)

theorem lowCount_nonneg (Γ : FiniteGame m n c r Seed) (j : Fin n)
    (x : ℝ) (ω : Sample m n r Seed) : 0 ≤ lowCount Γ j x ω := Nat.cast_nonneg _

theorem lowCount_le (Γ : FiniteGame m n c r Seed) (j : Fin n)
    (x : ℝ) (ω : Sample m n r Seed) : lowCount Γ j x ω ≤ c := by
  change (((playedAllocation Γ j ω ∩ Finset.univ.filter
    (fun i => Bayes.entryBid ((ω.1 i).2.val j) < x)).card : ℕ) : ℝ) ≤ (c : ℝ)
  exact_mod_cast (Finset.card_le_card Finset.inter_subset_left).trans
    (playedAllocation_card_le Γ j ω)

theorem integrable_lowCount (Γ : FiniteGame m n c r Seed) (j : Fin n) (x : ℝ) :
    Integrable (lowCount Γ j x) Γ.sampleLaw := by
  apply Integrable.of_bound (measurable_lowCount Γ j x).aestronglyMeasurable (c : ℝ)
  exact Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (lowCount_nonneg Γ j x ω)]
    exact lowCount_le Γ j x ω

def slotShortfall (j : Fin n) (x : ℝ) (d : Fin m → UserDraw n r) : ℝ :=
  max ((c : ℝ) - PiBinomial.count (aboveAt j x) Finset.univ d) 0

theorem measurable_slotShortfall (j : Fin n) (x : ℝ) :
    Measurable (slotShortfall (m := m) (r := r) (c := c) j x) :=
  (measurable_const.sub ((measurable_of_countable (fun k : ℕ => (k : ℝ))).comp
    (PiBinomial.measurable_count (aboveAt j x) (measurableSet_aboveAt j x) Finset.univ))).max
      measurable_const

theorem integrable_slotShortfall (Γ : FiniteGame m n c r Seed) (j : Fin n) (x : ℝ) :
    Integrable (slotShortfall (c := c) j x) (Measure.pi fun _ : Fin m => Γ.userLaw) := by
  apply Integrable.of_bound (measurable_slotShortfall j x).aestronglyMeasurable (c : ℝ)
  exact Eventually.of_forall fun d => by
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact max_le (sub_le_self _ (Nat.cast_nonneg _)) (Nat.cast_nonneg _)

theorem integrable_slotShortfall_sample (Γ : FiniteGame m n c r Seed)
    (j : Fin n) (x : ℝ) :
    Integrable (fun ω : Sample m n r Seed => slotShortfall (c := c) j x ω.1) Γ.sampleLaw := by
  apply Integrable.of_bound
    ((measurable_slotShortfall j x).comp measurable_fst).aestronglyMeasurable (c : ℝ)
  exact Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact max_le (sub_le_self _ (Nat.cast_nonneg _)) (Nat.cast_nonneg _)

theorem ae_lowCount_le_shortfall (Γ : FiniteGame m n c r Seed) (j : Fin n)
    (hT : UniformReserveRule Γ.seedLaw (Γ.policy j) r) (x : ℝ) :
    ∀ᵐ ω ∂Γ.sampleLaw, lowCount Γ j x ω ≤ slotShortfall (c := c) j x ω.1 := by
  classical
  have hset : MeasurableSet {ω : Sample m n r Seed |
      lowCount Γ j x ω ≤ slotShortfall (c := c) j x ω.1} :=
    measurableSet_le (measurable_lowCount Γ j x)
      ((measurable_slotShortfall j x).comp measurable_fst)
  apply (Measure.ae_prod_iff_ae_ae hset).mpr
  apply Eventually.of_forall
  intro d
  have ht := hT.ae_optimal Γ.reserve_nonneg (fun i => (d i).2.val j)
    (fun i b hb => (d i).2.property j b hb)
  have hs := (measurePreserving_eval (fun _ : Fin n => Γ.seedLaw) j).quasiMeasurePreserving.ae ht
  filter_upwards [hs] with s hs
  apply Finite.optimal_low_card_real_le_shortfall c _ _
    (Finset.univ.filter (fun i => d i ∈ aboveAt j x)) _ hs
  intro h hh l hl
  exact (Finset.mem_filter.mp hl).2 |>.trans ((Finset.mem_filter.mp hh).2.2)

theorem integral_lowCount_normalized_le (Γ : FiniteGame m n c r Seed) (hm : 0 < m)
    (j : Fin n) (hT : UniformReserveRule Γ.seedLaw (Γ.policy j) r)
    (δ x : ℝ) (hδ : 0 ≤ δ) (ht : (c : ℝ) / m - δ ≤ bidTail Γ j x) :
    (∫ ω, lowCount Γ j x ω ∂Γ.sampleLaw) / m ≤ δ + 1 / (2 * Real.sqrt m) := by
  have hh := integral_mono_ae (integrable_lowCount Γ j x)
    (integrable_slotShortfall_sample Γ j x) (ae_lowCount_le_shortfall Γ j hT x)
  have he : (∫ ω : Sample m n r Seed, slotShortfall (c := c) j x ω.1 ∂Γ.sampleLaw) =
      ∫ d, slotShortfall (c := c) j x d ∂(Measure.pi fun _ : Fin m => Γ.userLaw) := by
    simp only [FiniteGame.sampleLaw, integral_fun_fst, probReal_univ, one_smul]
  rw [he] at hh
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  apply (div_le_div_of_nonneg_right hh hmR.le).trans
  have ht' := PiBinomial.integral_normalized_shortfall_le Γ.userLaw (aboveAt j x)
    (measurableSet_aboveAt j x) (Finset.univ : Finset (Fin m)) (by simpa using hm)
    ((c : ℝ) / m) ((c : ℝ) / m) δ hδ ht
  simpa only [Finset.card_univ, Fintype.card_fin, sub_self, abs_zero, add_zero,
    mul_div_cancel₀ _ hmR.ne', slotShortfall] using ht'

end FCAppendix.CommonReserve
