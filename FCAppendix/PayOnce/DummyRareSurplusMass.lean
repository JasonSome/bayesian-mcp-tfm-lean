import FCAppendix.PayOnce.CompactWindowSelection
import FCAppendix.PayOnce.DummyRareSuccessRows
import FCAppendix.PayOnce.KernelDemand

namespace FCAppendix.PayOnce.DummyRareSuccess
open MeasureTheory ProbabilityTheory Filter Topology Set CommonList
open DummyKernel CompactifiedBidLaws CompactKernelRareSuccess VanishingBidIC

theorem tendsto_rare_surplus_mass_zero
    (N : ℕ → ℕ) (hNpos : ∀ t, 0 < N t) (hN : Tendsto N atTop atTop)
    {n : ℕ} (hn : 2 ≤ n)
    {Ω : ℕ → Type*} [∀ t, MeasurableSpace (Ω t)]
    (P : ∀ t, Measure (Ω t)) [∀ t, IsProbabilityMeasure (P t)]
    (b w : ∀ t, Ω t → ℝ) (hb : ∀ t, Measurable (b t))
    (G : ℕ → ProbabilityMeasure ℝ)
    (hmap : ∀ t, (G t : Measure ℝ) = (P t).map (b t))
    (hpos : ∀ t, ∀ᵐ y ∂(G t : Measure ℝ), 0 ≤ y)
    {G₀ : ProbabilityMeasure ENNReal}
    (hweak : Tendsto (fun t => scaledLaw (G t) 1) atTop (𝓝 G₀))
    {ρ L : ℝ} (hρ : 0 < ρ) (hL : 0 < L)
    (hroot : KernelDemand.demand n (G₀ : Measure ENNReal) L = ρ)
    (hunique : ∀ T : ℝ, 0 < T → KernelDemand.demand n (G₀ : Measure ENNReal) T = ρ → T = L)
    {c : ℕ → ℕ}
    (hcapacity : Tendsto (fun t => (c t:ℝ)/N t) atTop (𝓝 ρ))
    (T : ℕ → Set ℝ)
    (hgood : ∀ t, ∀ᵐ z ∂P t, 0 < b t z →
      b t z ∈ regularSupportedSet (ι := Fin (N t)) n (c t) (G t : Measure ℝ) (T t) ∧
      ∀ y ∈ T t, (w t z-y) * coverage n (c t) hn
          (Measure.pi (fun _ : Fin (N t) => (G t : Measure ℝ))) y ≤
        (w t z-b t z) * coverage n (c t) hn
          (Measure.pi (fun _ : Fin (N t) => (G t : Measure ℝ))) (b t z))
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    Tendsto (fun t => P t {z | δ ≤ w t z-b t z ∧ b t z ∈ Icc ε L}) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro r hr
    exact (not_lt_of_ge bot_le hr).elim
  · intro q hq
    by_contra hnot
    have hfreq : ∃ᶠ t in atTop, q ≤ P t {z | δ ≤ w t z-b t z ∧ b t z ∈ Icc ε L} := by
      simpa only [not_lt] using not_eventually.mp hnot
    obtain ⟨φ, hφ, hmass⟩ := extraction_of_frequently_atTop hfreq
    have hm t : (scaledLaw (G (φ t)) 1 : Measure ENNReal) =
        (P (φ t)).map (fun z => ENNReal.ofReal (b (φ t) z)) := by
      change (G (φ t) : Measure ℝ).map (fun y => ENNReal.ofReal (y/1)) = _
      simp only [div_one]
      rw [hmap, Measure.map_map ENNReal.measurable_ofReal (hb (φ t))]
      rfl
    obtain ⟨ψ, hψ, z, hz, x₀, hx, hsupp, hconv⟩ := exists_supported_window_subsequence
      (fun t => P (φ t)) (fun t => b (φ t)) (fun t => hb (φ t))
      (fun t => scaledLaw (G (φ t)) 1) G₀ hm (hweak.comp hφ.tendsto_atTop) isCompact_Icc
      (fun t z => 0 < b (φ t) z → b (φ t) z ∈ regularSupportedSet (ι := Fin (N (φ t))) n (c (φ t))
          (G (φ t) : Measure ℝ) (T (φ t)) ∧
        ∀ y ∈ T (φ t), (w (φ t) z-y) * coverage n (c (φ t)) hn
            (Measure.pi (fun _ : Fin (N (φ t)) => (G (φ t) : Measure ℝ))) y ≤
          (w (φ t) z-b (φ t) z) * coverage n (c (φ t)) hn
            (Measure.pi (fun _ : Fin (N (φ t)) => (G (φ t) : Measure ℝ))) (b (φ t) z))
      (fun t z => δ ≤ w (φ t) z-b (φ t) z) (fun t => hgood (φ t)) hq
      (Filter.Eventually.of_forall hmass)
    let θ := φ ∘ ψ
    have hθ : StrictMono θ := hφ.comp hψ
    have hchosen t := (hz t).1 (hε.trans_le (hz t).2.2.1)
    have hdemand s (hs : 0 < s) (hs1 : s ≤ 1) :
        ρ < ∫ b, KernelLawConvergence.compactKernel n b (x₀*H n s) ∂(G₀ : Measure ENNReal) :=
      demand_gt_of_unique_root hn (G₀ : Measure ENNReal) hL hroot hunique (hε.trans_le hx.1) hx.2 hs hs1
    have hsurplus := (surplus_tendsto_zero_of_supported_IC_rows (N ∘ θ)
      (fun t => hNpos (θ t)) (hN.comp hθ.tendsto_atTop) hn (G ∘ θ) (fun t => hpos (θ t))
      (hweak.comp hθ.tendsto_atTop)
      (fun t => (hchosen t).1) (hε.trans_le hx.1) hconv hρ hsupp hdemand
      (hcapacity.comp hθ.tendsto_atTop) (fun t => (hchosen t).2)).2
    exact hδ.not_ge (ge_of_tendsto hsurplus (Filter.Eventually.of_forall fun t => (hz t).2.1))

end FCAppendix.PayOnce.DummyRareSuccess
