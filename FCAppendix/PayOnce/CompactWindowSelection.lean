import FCAppendix.PayOnce.AnalyticalScaling
import Mathlib.Topology.MetricSpace.Thickening

namespace FCAppendix.PayOnce.VanishingBidIC
open MeasureTheory ProbabilityTheory Set Filter Topology

theorem exists_supported_window_subsequence
    {Ω : ℕ → Type*} [∀ t, MeasurableSpace (Ω t)]
    (P : ∀ t, Measure (Ω t)) [∀ t, IsProbabilityMeasure (P t)]
    (f : ∀ t, Ω t → ℝ) (hf : ∀ t, Measurable (f t))
    (L : ℕ → ProbabilityMeasure ENNReal) (G : ProbabilityMeasure ENNReal)
    (hmap : ∀ t, (L t : Measure ENNReal) = (P t).map (fun x => ENNReal.ofReal (f t x)))
    (hweak : Tendsto L atTop (𝓝 G))
    {K : Set ℝ} (hK : IsCompact K)
    (Good Block : ∀ t, Ω t → Prop) (hgood : ∀ t, ∀ᵐ x ∂P t, Good t x)
    {q : ENNReal} (hq : 0 < q)
    (hmass : ∀ᶠ t in atTop, q ≤ P t {x | Block t x ∧ f t x ∈ K}) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ x : ∀ j, Ω (φ j),
      (∀ j, Good (φ j) (x j) ∧ Block (φ j) (x j) ∧ f (φ j) (x j) ∈ K) ∧
      ∃ x₀ ∈ K, ENNReal.ofReal x₀ ∈ (G : Measure ENNReal).support ∧
        Tendsto (fun j => f (φ j) (x j)) atTop (𝓝 x₀) := by
  classical
  let S : Set ℝ := ENNReal.ofReal ⁻¹' (G : Measure ENNReal).support
  have hS : IsClosed S := (Measure.isClosed_support).preimage ENNReal.continuous_ofReal
  let δ : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1)
  have hδ j : 0 < δ j := by dsimp only [δ]; positivity
  have hev j : ∀ᶠ t in atTop, ∃ x : Ω t,
      Good t x ∧ Block t x ∧ f t x ∈ K ∧ f t x ∈ Metric.thickening (δ j) S := by
    let C := ENNReal.ofReal '' (K \ Metric.thickening (δ j) S)
    have hC : IsCompact C :=
      (hK.inter_right Metric.isOpen_thickening.isClosed_compl).image ENNReal.continuous_ofReal
    have hzero : (G : Measure ENNReal) C = 0 := by
      apply measure_mono_null _ (Measure.measure_compl_support (μ := (G : Measure ENNReal)))
      rintro b ⟨r, ⟨hrK, hr⟩, rfl⟩ hb
      exact hr (Metric.self_subset_thickening (hδ j) S hb)
    have hlim := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hweak hC.isClosed
    rw [hzero] at hlim
    have hsmall := eventually_lt_of_limsup_lt (hlim.trans_lt hq)
    filter_upwards [hsmall, hmass] with t ht hm
    by_contra hn
    have hinc : {x | Block t x ∧ f t x ∈ K} ≤ᵐ[P t]
        (fun x => ENNReal.ofReal (f t x)) ⁻¹' C := by
      filter_upwards [hgood t] with x hx hxB
      refine ⟨f t x, ⟨hxB.2, ?_⟩, rfl⟩
      intro hs
      exact hn ⟨x, hx, hxB.1, hxB.2, hs⟩
    have hle := hm.trans (measure_mono_ae hinc)
    rw [← Measure.map_apply (show Measurable (fun x => ENNReal.ofReal (f t x)) from
      ENNReal.measurable_ofReal.comp (hf t)) hC.isClosed.measurableSet,
      ← hmap t] at hle
    exact ht.not_ge hle
  choose N hN using fun j => eventually_atTop.mp (hev j)
  let φ : ℕ → ℕ := Nat.rec (N 0) (fun j r => max (N (j+1)) (r+1))
  have hφN j : N j ≤ φ j := by
    cases j with
    | zero => exact le_rfl
    | succ j => exact le_max_left _ _
  have hφ : StrictMono φ := strictMono_nat_of_lt_succ fun j => by
    exact (Nat.lt_succ_self (φ j)).trans_le (le_max_right _ _)
  choose x hxgood hxB hxK hxS using fun j => hN j (φ j) (hφN j)
  obtain ⟨x₀, hx₀, ψ, hψ, hconv⟩ := hK.isSeqCompact hxK
  choose y hyS hydist using fun j => Metric.mem_thickening_iff.mp (hxS (ψ j))
  have hdist : Tendsto (fun j => dist (f (φ (ψ j)) (x (ψ j))) (y j)) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => dist_nonneg) (fun j => (hydist j).le)
    exact tendsto_one_div_add_atTop_nhds_zero_nat.comp hψ.tendsto_atTop
  have hyconv : Tendsto y atTop (𝓝 x₀) := hconv.congr_dist hdist
  refine ⟨φ ∘ ψ, hφ.comp hψ, fun j => x (ψ j), ?_, x₀, hx₀, ?_, hconv⟩
  · exact fun j => ⟨hxgood (ψ j), hxB (ψ j), hxK (ψ j)⟩
  · exact hS.mem_of_tendsto hyconv (Filter.Eventually.of_forall hyS)

end FCAppendix.PayOnce.VanishingBidIC
