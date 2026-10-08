import FCAppendix.Finite.PPIVisibleRanks
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.Topology.Order.Compact

noncomputable section
namespace FCAppendix.Ample.RankMeasureTools
open MeasureTheory Set Filter Topology
open scoped ENNReal BigOperators

theorem strict_tail_sub {μ : Measure ℝ} [IsFiniteMeasure μ]
    {u v : ℝ} (huv : u ≤ v) :
    μ.real (Ioi u) - μ.real (Ioi v) = μ.real (Ioc u v) := by
  rw [← measureReal_sdiff (Ioi_subset_Ioi huv) measurableSet_Ioi]
  congr 1
  ext x
  simp only [Set.mem_sdiff, mem_Ioi, mem_Ioc, not_lt]

theorem bounded_tail_eq {μ : Measure ℝ} [IsFiniteMeasure μ] (h u : ℝ) :
    μ.real (Ioc u h) = μ.real (Ioi u) - μ.real (Ioi (max u h)) := by
  rw [strict_tail_sub (le_max_left u h)]
  by_cases huh : u ≤ h
  · rw [max_eq_right huh]
  · have hhu : h < u := lt_of_not_ge huh
    rw [max_eq_left hhu.le, Ioc_self, measureReal_empty,
      Ioc_eq_empty_of_le hhu.le, measureReal_empty]

theorem continuous_strict_tail (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hatom : ∀ u : ℝ, μ {u} = 0) :
    Continuous (fun u : ℝ => μ.real (Ioi u)) := by
  exact continuous_iff_continuousAt.mpr
    (fun u => FCAppendix.Bayes.continuousAt_real_tail_of_no_atom μ u (hatom u))

theorem continuous_bounded_tail (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hatom : ∀ u : ℝ, μ {u} = 0) (h : ℝ) :
    Continuous (fun u : ℝ => μ.real (Ioc u h)) := by
  have hc := continuous_strict_tail μ hatom
  have he : (fun u : ℝ => μ.real (Ioc u h)) =
      (fun u => μ.real (Ioi u) - μ.real (Ioi (max u h))) := by
    funext u
    exact bounded_tail_eq h u
  rw [he]
  exact hc.sub (hc.comp (continuous_id.max continuous_const))

theorem closed_set_null_of_interval_null (μ : Measure ℝ)
    (hatom : ∀ u : ℝ, μ {u} = 0) {E : Set ℝ} (hE : IsClosed E)
    (hinterval : ∀ u ∈ E, ∀ v ∈ E, u ≤ v → μ (Ioc u v) = 0) :
    μ E = 0 := by
  classical
  let K : ℕ → Set ℝ := fun m => Icc (-(m : ℝ)) (m : ℝ) ∩ E
  have hK (m : ℕ) : μ (K m) = 0 := by
    by_cases hne : (K m).Nonempty
    · have hcompact : IsCompact (K m) := isCompact_Icc.inter_right hE
      obtain ⟨a, ha⟩ := hcompact.exists_isLeast hne
      obtain ⟨b, hb⟩ := hcompact.exists_isGreatest hne
      have hab : a ≤ b := ha.2 hb.1
      have hIoc := hinterval a ha.1.2 b hb.1.2 hab
      have hcover : K m ⊆ {a} ∪ Ioc a b := by
        intro x hx
        by_cases hax : x = a
        · exact Or.inl hax
        · exact Or.inr ⟨lt_of_le_of_ne (ha.2 hx) (Ne.symm hax), hb.2 hx⟩
      exact measure_mono_null hcover (measure_union_null (hatom a) hIoc)
    · rw [Set.not_nonempty_iff_eq_empty.mp hne, measure_empty]
  have hcover : E ⊆ ⋃ m : ℕ, K m := by
    intro x hx
    obtain ⟨m, hm⟩ := exists_nat_gt |x|
    apply mem_iUnion.mpr
    refine ⟨m, ⟨?_, ?_⟩, hx⟩
    · have := neg_abs_le x
      linarith
    · exact (le_abs_self x).trans hm.le
  exact measure_mono_null hcover (measure_iUnion_null hK)

theorem continuous_level_null (μ : Measure ℝ)
    (hatom : ∀ u : ℝ, μ {u} = 0) {A : ℝ → ℝ} (hA : Continuous A)
    (hinterval : ∀ u v : ℝ, u ≤ v → A u = A v → μ (Ioc u v) = 0)
    (a : ℝ) : μ {u | A u = a} = 0 := by
  apply closed_set_null_of_interval_null μ hatom (isClosed_eq hA continuous_const)
  intro u hu v hv huv
  exact hinterval u v huv (hu.trans hv.symm)

theorem strict_tail_pos_ae (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hatom : ∀ u : ℝ, μ {u} = 0) :
    ∀ᵐ u ∂μ, 0 < μ.real (Ioi u) := by
  have hz : μ {u | μ.real (Ioi u) = 0} = 0 := by
    apply closed_set_null_of_interval_null μ hatom
      (isClosed_eq (continuous_strict_tail μ hatom) continuous_const)
    intro u hu v _huv _huv'
    exact measure_mono_null (fun _ hx => hx.1)
      ((measureReal_eq_zero_iff (measure_ne_top _ _)).mp hu)
  rw [ae_iff]
  exact measure_mono_null
    (fun u hu => le_antisymm (le_of_not_gt hu) measureReal_nonneg) hz

theorem strict_tail_eq_bounded_tail {μ : Measure ℝ} [IsFiniteMeasure μ]
    {h : ℝ} (hs : ∀ᵐ u ∂μ, u ≤ h) (u : ℝ) :
    μ.real (Ioi u) = μ.real (Ioc u h) := by
  apply measureReal_congr
  filter_upwards [hs] with x hx
  change (u < x) = (u < x ∧ x ≤ h)
  exact propext ⟨fun hux => ⟨hux, hx⟩, fun hux => hux.1⟩

theorem bounded_tail_pos_ae (μ : Measure ℝ) [IsFiniteMeasure μ]
    {h : ℝ} (hatom : ∀ u : ℝ, μ {u} = 0)
    (hs : ∀ᵐ u ∂μ, u ∈ Ioc 0 h) :
    ∀ᵐ u ∂μ, 0 < u ∧ u < h ∧ 0 < μ.real (Ioc u h) := by
  have hne : ∀ᵐ u ∂μ, u ≠ h := by
    rw [ae_iff]
    simpa using hatom h
  have hupper := hs.mono (fun _ hu => hu.2)
  filter_upwards [hs, hne, strict_tail_pos_ae μ hatom] with u hu hne hpos
  exact ⟨hu.1, lt_of_le_of_ne hu.2 hne,
    (strict_tail_eq_bounded_tail hupper u) ▸ hpos⟩

theorem strictOn_level_null (μ : Measure ℝ)
    (hatom : ∀ u : ℝ, μ {u} = 0) {P : ℝ → Prop} {A : ℝ → ℝ}
    (hstrict : ∀ u, P u → ∀ v, P v → u < v → A u < A v) (a : ℝ) :
    μ {u | P u ∧ A u = a} = 0 := by
  classical
  by_cases hne : {u | P u ∧ A u = a}.Nonempty
  · obtain ⟨u, hu⟩ := hne
    apply measure_mono_null (t := {u}) _ (hatom u)
    intro v hv
    show v = u
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have := hstrict v hv.1 u hu.1 hlt
      rw [hv.2, hu.2] at this
      exact (lt_irrefl a) this
    · have := hstrict u hu.1 v hv.1 hgt
      rw [hv.2, hu.2] at this
      exact (lt_irrefl a) this
  · rw [Set.not_nonempty_iff_eq_empty.mp hne, measure_empty]

theorem strictOn_gt_ae (μ : Measure ℝ)
    (hatom : ∀ u : ℝ, μ {u} = 0) {P : ℝ → Prop} {A : ℝ → ℝ} {a : ℝ}
    (hP : ∀ᵐ u ∂μ, P u) (hge : ∀ᵐ u ∂μ, a ≤ A u)
    (hstrict : ∀ u, P u → ∀ v, P v → u < v → A u < A v) :
    ∀ᵐ u ∂μ, a < A u := by
  have hne : ∀ᵐ u ∂μ, ¬ (P u ∧ A u = a) := by
    rw [ae_iff]
    simpa only [not_not] using strictOn_level_null μ hatom hstrict a
  filter_upwards [hP, hge, hne] with u hu hle hne
  exact lt_of_le_of_ne hle (fun he => hne ⟨hu, he.symm⟩)

theorem finite_tendsto_integral_of_unit_support {α : Type*} {l : Filter α}
    {ν : α → FiniteMeasure ℝ} {μ : FiniteMeasure ℝ}
    (hν : ∀ a, ∀ᵐ x ∂(ν a : Measure ℝ), x ∈ Icc (0 : ℝ) 1)
    (hμ : ∀ᵐ x ∂(μ : Measure ℝ), x ∈ Icc (0 : ℝ) 1)
    (hweak : Tendsto ν l (𝓝 μ)) {f : ℝ → ℝ} (hf : Continuous f) :
    Tendsto (fun a => ∫ x, f x ∂(ν a : Measure ℝ)) l
      (𝓝 (∫ x, f x ∂(μ : Measure ℝ))) := by
  let clip : C(ℝ, Icc (0 : ℝ) 1) :=
    ⟨fun x => ⟨max 0 (min 1 x), le_max_left _ _,
        max_le (by norm_num) (min_le_left _ _)⟩,
      (continuous_const.max (continuous_const.min continuous_id)).subtype_mk _⟩
  let test : BoundedContinuousFunction ℝ ℝ :=
    (BoundedContinuousFunction.mkOfCompact
      (⟨fun x : Icc (0 : ℝ) 1 => f x, hf.comp continuous_subtype_val⟩ :
        C(Icc (0 : ℝ) 1, ℝ))).compContinuous clip
  have heq : ∀ x ∈ Icc (0 : ℝ) 1, test x = f x := by
    intro x hx
    change f (max 0 (min 1 x)) = f x
    rw [min_eq_right hx.2, max_eq_right hx.1]
  have hi (κ : FiniteMeasure ℝ)
      (hκ : ∀ᵐ x ∂(κ : Measure ℝ), x ∈ Icc (0 : ℝ) 1) :
      (∫ x, test x ∂(κ : Measure ℝ)) = ∫ x, f x ∂(κ : Measure ℝ) :=
    integral_congr_ae (hκ.mono fun x hx => heq x hx)
  have ht := (FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hweak) test
  simpa only [hi μ hμ, hi _ (hν _)] using ht

end FCAppendix.Ample.RankMeasureTools
