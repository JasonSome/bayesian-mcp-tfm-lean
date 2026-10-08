import FCAppendix.Ample.CommonRateActualAdapters
import FCAppendix.Ample.RankDistributionTransform

noncomputable section
namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology
open scoped ENNReal BigOperators
open Ample Ample.RankMeasureTools

variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

def ascendingBidRank (Γ : FiniteGame m n c Seed) (b : ℝ) : ℝ :=
  (Γ.F ⊗ₘ Γ.σ).real {x | 0 < x.2.bid ∧ x.2.bid ≤ b ∧ 0 < x.2.routeCount}

def rankClassLaw (Γ : FiniteGame m n c Seed) (j : ℕ) : Measure ℝ :=
  ((Γ.F ⊗ₘ Γ.σ).restrict
    {x | 0 < x.2.bid ∧ x.2.routeCount = j}).map
      (fun x => ascendingBidRank Γ x.2.bid)

def rankTail (nu : ℕ → Measure ℝ) (h : ℝ) (u : ℝ) (j : ℕ) : ℝ :=
  (nu j).real (Ioc u h)

structure RankLimit {M C : ℕ → ℕ}
    (Γ : ∀ t, FiniteGame (M t) n (C t) Seed)
    (pi : ℕ → ℝ) (h : ℝ) (nu : ℕ → Measure ℝ) : Prop where
  dominated : ∀ j ∈ Finset.Icc 1 n, nu j ≤ volume.restrict (Ioc 0 h)
  sum_law : (∑ j ∈ Finset.Icc 1 n, nu j) = volume.restrict (Ioc 0 h)
  mass : ∀ j ∈ Finset.Icc 1 n, (nu j).real univ = pi j
  weak : ∀ j ∈ Finset.Icc 1 n, ∀ f : ℝ → ℝ, Continuous f →
    Tendsto (fun t => ∫ u, f u ∂rankClassLaw (Γ t) j) atTop
      (𝓝 (∫ u, f u ∂nu j))
  tails : ∀ eps > 0, ∀ᶠ t in atTop, ∀ j ∈ Finset.Icc 1 n,
    ∀ u ∈ Icc 0 h,
      |(rankClassLaw (Γ t) j).real (Ioi u) - rankTail nu h u j| < eps

def positiveRankLaw (Γ : FiniteGame m n c Seed) : Measure ℝ :=
  ((Γ.F ⊗ₘ Γ.σ).restrict
    {x | 0 < x.2.bid ∧ 0 < x.2.routeCount}).map
      (fun x => ascendingBidRank Γ x.2.bid)

theorem ascendingBidRank_monotone (Γ : FiniteGame m n c Seed) :
    Monotone (ascendingBidRank Γ) := by
  intro b d hbd
  exact measureReal_mono (fun x hx => ⟨hx.1, hx.2.1.trans hbd, hx.2.2⟩)

theorem measurable_ascendingBidRank (Γ : FiniteGame m n c Seed) :
    Measurable (ascendingBidRank Γ) := (ascendingBidRank_monotone Γ).measurable

theorem measurable_drawRank (Γ : FiniteGame m n c Seed) :
    Measurable (fun x : ℝ × JointAction n => ascendingBidRank Γ x.2.bid) :=
  (measurable_ascendingBidRank Γ).comp ((measurable_bid n).comp measurable_snd)

theorem ascendingBidRank_nonneg (Γ : FiniteGame m n c Seed) (b : ℝ) :
    0 ≤ ascendingBidRank Γ b := measureReal_nonneg

theorem ascendingBidRank_le_participation (Γ : FiniteGame m n c Seed) (b : ℝ) :
    ascendingBidRank Γ b ≤ positiveRouteMass Γ (fun _ => True) := by
  exact measureReal_mono (fun x hx => ⟨hx.1, hx.2.2, trivial⟩)

theorem positiveRouteMass_le_one_rank (Γ : FiniteGame m n c Seed) :
    positiveRouteMass Γ (fun _ => True) ≤ 1 := by
  calc
    _ ≤ (Γ.F ⊗ₘ Γ.σ).real univ := measureReal_mono (subset_univ _)
    _ = 1 := by simp [Measure.real]

theorem ascendingBidRank_le_one (Γ : FiniteGame m n c Seed) (b : ℝ) :
    ascendingBidRank Γ b ≤ 1 :=
  (ascendingBidRank_le_participation Γ b).trans (positiveRouteMass_le_one_rank Γ)

instance rankClassLaw_finite (Γ : FiniteGame m n c Seed) (j : ℕ) :
    IsFiniteMeasure (rankClassLaw Γ j) := by
  unfold rankClassLaw
  infer_instance

instance positiveRankLaw_finite (Γ : FiniteGame m n c Seed) :
    IsFiniteMeasure (positiveRankLaw Γ) := by
  unfold positiveRankLaw
  infer_instance

theorem ascendingBidRank_eq_stratum (Γ : FiniteGame m n c Seed)
    (hatom : PositiveVisibleAtomless Γ) (b : ℝ) :
    ascendingBidRank Γ b = (positiveBidStratum Γ hatom (fun _ => True)).rank b := by
  rw [(positiveBidStratum Γ hatom (fun _ => True)).rank_eq_lower_mass
    ((measurable_bid n).comp measurable_snd)]
  unfold ascendingBidRank
  congr 1
  ext x
  simp only [positiveBidStratum, mem_inter_iff, mem_setOf_eq]
  tauto

theorem ascendingBidRank_continuous (Γ : FiniteGame m n c Seed)
    (hatom : PositiveVisibleAtomless Γ) : Continuous (ascendingBidRank Γ) := by
  have he : ascendingBidRank Γ =
      (positiveBidStratum Γ hatom (fun _ => True)).rank := by
    funext b
    exact ascendingBidRank_eq_stratum Γ hatom b
  rw [he]
  exact (positiveBidStratum Γ hatom (fun _ => True)).continuous_rank
    ((measurable_bid n).comp measurable_snd)

theorem positiveBidMarginal_atomless (Γ : FiniteGame m n c Seed)
    (hatom : PositiveVisibleAtomless Γ) (b : ℝ) :
    (((Γ.F ⊗ₘ Γ.σ).restrict {x | 0 < x.2.bid ∧ 0 < x.2.routeCount}).map
      (fun x => x.2.bid)) {b} = 0 := by
  simpa only [BidStratum.bidMeasure, positiveBidStratum, and_true] using
    (positiveBidStratum Γ hatom (fun _ => True)).bidMeasure_atom
      ((measurable_bid n).comp measurable_snd) b

theorem positiveRankLaw_eq_volume (Γ : FiniteGame m n c Seed)
    (hatom : PositiveVisibleAtomless Γ) :
    positiveRankLaw Γ = volume.restrict (Ioc 0 (positiveRouteMass Γ (fun _ => True))) := by
  have he : positiveRankLaw Γ =
      (positiveBidStratum Γ hatom (fun _ => True)).rankMeasure
        ((measurable_bid n).comp measurable_snd) := by
    unfold positiveRankLaw BidStratum.rankMeasure
    simp only [positiveBidStratum, and_true]
    congr 1
    funext x
    simpa only [positiveBidStratum, and_true] using
      ascendingBidRank_eq_stratum Γ hatom x.2.bid
  rw [he, BidStratum.rankMeasure_eq_volume, positiveBidStratum_mass]

theorem rank_finite_sum_real {ι : Type*} (s : Finset ι) (μ : ι → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] (A : Set ℝ) :
    (∑ i ∈ s, μ i).real A = ∑ i ∈ s, (μ i).real A := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, measureReal_add_apply, ih, Finset.sum_insert hi]

theorem rankClassLaw_real_apply (Γ : FiniteGame m n c Seed) (j : ℕ)
    (A : Set ℝ) (hA : MeasurableSet A) :
    (rankClassLaw Γ j).real A =
      (Γ.F ⊗ₘ Γ.σ).real {x | 0 < x.2.bid ∧ x.2.routeCount = j ∧
        ascendingBidRank Γ x.2.bid ∈ A} := by
  unfold rankClassLaw
  rw [map_measureReal_apply (measurable_drawRank Γ) hA,
    measureReal_restrict_apply ((measurable_drawRank Γ) hA)]
  congr 1
  ext x
  simp only [mem_inter_iff, mem_preimage, mem_setOf_eq]
  tauto

theorem positiveRankLaw_real_apply (Γ : FiniteGame m n c Seed)
    (A : Set ℝ) (hA : MeasurableSet A) :
    (positiveRankLaw Γ).real A =
      (Γ.F ⊗ₘ Γ.σ).real {x | 0 < x.2.bid ∧ 0 < x.2.routeCount ∧
        ascendingBidRank Γ x.2.bid ∈ A} := by
  unfold positiveRankLaw
  rw [map_measureReal_apply (measurable_drawRank Γ) hA,
    measureReal_restrict_apply ((measurable_drawRank Γ) hA)]
  congr 1
  ext x
  simp only [mem_inter_iff, mem_preimage, mem_setOf_eq]
  tauto

theorem sum_rankClassLaw (Γ : FiniteGame m n c Seed) :
    (∑ j ∈ Finset.Icc 1 n, rankClassLaw Γ j) = positiveRankLaw Γ := by
  classical
  apply Measure.ext
  intro A hA
  apply (measureReal_eq_measureReal_iff (by finiteness) (by finiteness)).mp
  rw [rank_finite_sum_real, positiveRankLaw_real_apply Γ A hA]
  simp_rw [rankClassLaw_real_apply Γ _ A hA]
  let E : ℕ → Set (ℝ × JointAction n) := fun j =>
    {x | 0 < x.2.bid ∧ x.2.routeCount = j ∧ ascendingBidRank Γ x.2.bid ∈ A}
  have hE (j : ℕ) : MeasurableSet (E j) :=
    (measurableSet_lt measurable_const ((measurable_bid n).comp measurable_snd)).inter
      ((measurableSet_eq_fun ((measurable_routeCount n).comp measurable_snd)
        measurable_const).inter ((measurable_drawRank Γ) hA))
  have hd : Set.PairwiseDisjoint (↑(Finset.Icc 1 n)) E := by
    intro i _ j _ hij
    apply disjoint_left.mpr
    intro x hx hy
    exact hij (hx.2.1.symm.trans hy.2.1)
  rw [← measureReal_biUnion_finset hd (fun j _ => hE j)]
  congr 1
  ext x
  simp only [mem_iUnion, mem_setOf_eq]
  constructor
  · rintro ⟨j, hj, hbid, hjx, hAx⟩
    refine ⟨hbid, ?_, hAx⟩
    have := (Finset.mem_Icc.mp hj).1
    omega
  · rintro ⟨hbid, hk, hAx⟩
    exact ⟨x.2.routeCount, Finset.mem_Icc.mpr ⟨hk, x.2.routeCount_le⟩,
      hbid, rfl, hAx⟩

theorem rankClassLaw_le_positiveRankLaw (Γ : FiniteGame m n c Seed)
    {j : ℕ} (hj : 1 ≤ j) : rankClassLaw Γ j ≤ positiveRankLaw Γ := by
  unfold rankClassLaw positiveRankLaw
  apply Measure.map_mono _ (measurable_drawRank Γ)
  apply Measure.restrict_mono_set
  intro x hx
  have hjx : x.2.routeCount = j := hx.2
  exact ⟨hx.1, by omega⟩

theorem rankClassLaw_dominated (Γ : FiniteGame m n c Seed)
    (hatom : PositiveVisibleAtomless Γ) {j : ℕ} (hj : 1 ≤ j) :
    rankClassLaw Γ j ≤ volume.restrict (Ioc 0 (positiveRouteMass Γ (fun _ => True))) := by
  rw [← positiveRankLaw_eq_volume Γ hatom]
  exact rankClassLaw_le_positiveRankLaw Γ hj

theorem rankClassLaw_unit_support (Γ : FiniteGame m n c Seed) (j : ℕ) :
    ∀ᵐ u ∂rankClassLaw Γ j, u ∈ Icc (0 : ℝ) 1 := by
  apply (ae_map_iff (measurable_drawRank Γ).aemeasurable measurableSet_Icc).mpr
  exact ae_of_all _ (fun x => ⟨ascendingBidRank_nonneg Γ _, ascendingBidRank_le_one Γ _⟩)

theorem rankClassLaw_mass_le_one (Γ : FiniteGame m n c Seed) (j : ℕ) :
    (rankClassLaw Γ j).real univ ≤ 1 := by
  rw [rankClassLaw_real_apply Γ j univ MeasurableSet.univ]
  calc
    _ ≤ (Γ.F ⊗ₘ Γ.σ).real univ := measureReal_mono (subset_univ _)
    _ = 1 := by simp [Measure.real]

theorem rankClassLaw_mass (Γ : FiniteGame m n c Seed) {j : ℕ} (hj : 1 ≤ j) :
    (rankClassLaw Γ j).real univ = positiveRouteMass Γ (fun k => k = j) := by
  rw [rankClassLaw_real_apply Γ j univ MeasurableSet.univ]
  unfold positiveRouteMass
  congr 1
  ext x
  simp only [mem_setOf_eq, mem_univ, and_true]
  constructor
  · intro hx
    exact ⟨hx.1, by omega, hx.2⟩
  · intro hx
    exact ⟨hx.1, hx.2.2⟩

end FCAppendix.Bayes
