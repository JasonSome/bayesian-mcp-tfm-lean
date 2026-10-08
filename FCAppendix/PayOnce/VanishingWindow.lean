import FCAppendix.PayOnce.CompactWindowSelection
import FCAppendix.PayOnce.VanishingScale

namespace FCAppendix.PayOnce.AnalyticalRareSuccess
open MeasureTheory ProbabilityTheory Filter Topology Set
open CommonList AnalyticalKernel CompactifiedBidLaws VanishingBidIC

theorem not_persistent_vanishing_window
    (N : ℕ → ℕ) (hNpos : ∀ t, 0 < N t) (hN : Tendsto N atTop atTop)
    {n : ℕ} (hn : 2 ≤ n)
    {Ω : ℕ → Type*} [∀ t, MeasurableSpace (Ω t)]
    (P : ∀ t, Measure (Ω t)) [∀ t, IsProbabilityMeasure (P t)]
    (b w : ∀ t, Ω t → ℝ) (hb : ∀ t, Measurable (b t))
    (G : ℕ → ProbabilityMeasure ℝ)
    (hmap : ∀ t, (G t : Measure ℝ) = (P t).map (b t))
    (hpos : ∀ t, ∀ᵐ x ∂P t, 0 < b t x)
    (a : ℕ → ℝ) (ha : ∀ t, 0 < a t) (ha0 : Tendsto a atTop (𝓝 0))
    {Gorig Gscaled : ProbabilityMeasure ENNReal}
    (hweakOrig : Tendsto (fun t => scaledLaw (G t) 1) atTop (𝓝 Gorig))
    (hweakScaled : Tendsto (fun t => scaledLaw (G t) (a t)) atTop (𝓝 Gscaled))
    {u ρ : ℝ} (hu : 0 < u) (hρ : 0 < ρ)
    (hmassOrig : ρ < (Gorig : Measure ENNReal).real (Ioi (ENNReal.ofReal u)))
    {c : ℕ → ℕ} (hc : ∀ t, c t ≤ Fintype.card (Fin (N t)) + 1)
    (hcapacity : Tendsto (fun t => (c t : ℝ) / N t) atTop (𝓝 ρ))
    (T : ℕ → Set ℝ) (hT : ∀ t y, y ∈ T t → 0 < y)
    (hgood : ∀ t, ∀ᵐ z ∂P t,
      b t z / a t ∈ regularSupportedSet (ι := Fin (N t)) n (c t)
        (rescaledRealLaw (G t) (a t) : Measure ℝ) ((fun y => y / a t) '' T t) ∧
      ∀ y ∈ T t, (w t z-y) * coverage n (c t) hn (hc t)
          (Measure.pi (fun _ : Fin (N t) => (G t : Measure ℝ))) y ≤
        (w t z-b t z) * coverage n (c t) hn (hc t)
          (Measure.pi (fun _ : Fin (N t) => (G t : Measure ℝ))) (b t z))
    {K : Set ℝ} (hK : IsCompact K) (hKpos : K ⊆ Ioi 0)
    {v : ℝ} (hv : 0 < v) {q : ENNReal} (hq : 0 < q)
    (hmass : ∀ᶠ t in atTop, q ≤ P t {z | v ≤ w t z ∧ b t z / a t ∈ K}) : False := by
  have hm t : (scaledLaw (G t) (a t) : Measure ENNReal) =
      (P t).map (fun z => ENNReal.ofReal (b t z / a t)) := by
    change (G t : Measure ℝ).map (fun y => ENNReal.ofReal (y / a t)) = _
    rw [hmap t, Measure.map_map (show Measurable (fun y : ℝ => ENNReal.ofReal (y / a t)) from
      ENNReal.measurable_ofReal.comp (measurable_id.div_const _)) (hb t)]
    rfl
  obtain ⟨φ, hφ, z, hz, x₀, hxK, hsupport, hconv⟩ :=
    exists_supported_window_subsequence P (fun t z => b t z / a t)
      (fun t => (hb t).div_const (a t)) (fun t => scaledLaw (G t) (a t)) Gscaled hm
      hweakScaled hK (fun t z => 0 < b t z ∧
        b t z / a t ∈ regularSupportedSet (ι := Fin (N t)) n (c t)
          (rescaledRealLaw (G t) (a t) : Measure ℝ) ((fun y => y / a t) '' T t) ∧
        ∀ y ∈ T t, (w t z-y) * coverage n (c t) hn (hc t)
            (Measure.pi (fun _ : Fin (N t) => (G t : Measure ℝ))) y ≤
          (w t z-b t z) * coverage n (c t) hn (hc t)
            (Measure.pi (fun _ : Fin (N t) => (G t : Measure ℝ))) (b t z))
      (fun t z => v ≤ w t z) (fun t => (hpos t).and (hgood t)) hq hmass
  have hGpos t : ∀ᵐ y ∂(G t : Measure ℝ), 0 < y := by
    rw [hmap t]
    exact (ae_map_iff (hb t).aemeasurable measurableSet_Ioi).mpr (hpos t)
  have hw := value_tendsto_zero_of_vanishing_scale (N ∘ φ) (fun t => hNpos (φ t))
    (hN.comp hφ.tendsto_atTop) hn (G ∘ φ) (fun t => hGpos (φ t))
    (a ∘ φ) (fun t => ha (φ t)) (ha0.comp hφ.tendsto_atTop)
    (hweakOrig.comp hφ.tendsto_atTop) (hweakScaled.comp hφ.tendsto_atTop) hu hρ hmassOrig
    (fun t => hc (φ t)) (hcapacity.comp hφ.tendsto_atTop) (T ∘ φ)
    (fun t y hy => hT (φ t) y hy) (fun t => b (φ t) (z t)) (fun t => w (φ t) (z t))
    (fun t => (hz t).1.1) (hKpos hxK) hconv hsupport
    (fun t => (hz t).1.2.1) (fun t => (hz t).1.2.2)
  exact hv.not_ge (ge_of_tendsto hw (Filter.Eventually.of_forall fun t => (hz t).2.1))

theorem tendsto_vanishing_window_mass_zero
    (N : ℕ → ℕ) (hNpos : ∀ t, 0 < N t) (hN : Tendsto N atTop atTop)
    {n : ℕ} (hn : 2 ≤ n)
    {Ω : ℕ → Type*} [∀ t, MeasurableSpace (Ω t)]
    (P : ∀ t, Measure (Ω t)) [∀ t, IsProbabilityMeasure (P t)]
    (b w : ∀ t, Ω t → ℝ) (hb : ∀ t, Measurable (b t))
    (G : ℕ → ProbabilityMeasure ℝ)
    (hmap : ∀ t, (G t : Measure ℝ) = (P t).map (b t))
    (hpos : ∀ t, ∀ᵐ x ∂P t, 0 < b t x)
    (a : ℕ → ℝ) (ha : ∀ t, 0 < a t) (ha0 : Tendsto a atTop (𝓝 0))
    {Gorig : ProbabilityMeasure ENNReal}
    (hweakOrig : Tendsto (fun t => scaledLaw (G t) 1) atTop (𝓝 Gorig))
    {u ρ : ℝ} (hu : 0 < u) (hρ : 0 < ρ)
    (hmassOrig : ρ < (Gorig : Measure ENNReal).real (Ioi (ENNReal.ofReal u)))
    {c : ℕ → ℕ} (hc : ∀ t, c t ≤ Fintype.card (Fin (N t)) + 1)
    (hcapacity : Tendsto (fun t => (c t : ℝ) / N t) atTop (𝓝 ρ))
    (T : ℕ → Set ℝ) (hT : ∀ t y, y ∈ T t → 0 < y)
    (hgood : ∀ t, ∀ᵐ z ∂P t,
      b t z / a t ∈ regularSupportedSet (ι := Fin (N t)) n (c t)
        (rescaledRealLaw (G t) (a t) : Measure ℝ) ((fun y => y / a t) '' T t) ∧
      ∀ y ∈ T t, (w t z-y) * coverage n (c t) hn (hc t)
          (Measure.pi (fun _ : Fin (N t) => (G t : Measure ℝ))) y ≤
        (w t z-b t z) * coverage n (c t) hn (hc t)
          (Measure.pi (fun _ : Fin (N t) => (G t : Measure ℝ))) (b t z))
    {K : Set ℝ} (hK : IsCompact K) (hKpos : K ⊆ Ioi 0)
    {v : ℝ} (hv : 0 < v) :
    Tendsto (fun t => P t {z | v ≤ w t z ∧ b t z / a t ∈ K}) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro r hr
    exact (not_lt_of_ge bot_le hr).elim
  · intro q hq
    by_contra hnot
    have hfreq : ∃ᶠ t in atTop, q ≤ P t {z | v ≤ w t z ∧ b t z / a t ∈ K} := by
      simpa only [not_lt] using not_eventually.mp hnot
    obtain ⟨φ, hφ, hmass⟩ := extraction_of_frequently_atTop hfreq
    obtain ⟨Gscaled, ψ, hψ, hweakScaled⟩ := exists_scaled_subsequence (G ∘ φ) (a ∘ φ)
    let θ := φ ∘ ψ
    have hθ : StrictMono θ := hφ.comp hψ
    exact not_persistent_vanishing_window (N ∘ θ) (fun t => hNpos (θ t))
      (hN.comp hθ.tendsto_atTop) hn (fun t => P (θ t))
      (fun t => b (θ t)) (fun t => w (θ t)) (fun t => hb (θ t))
      (G ∘ θ) (fun t => hmap (θ t)) (fun t => hpos (θ t))
      (a ∘ θ) (fun t => ha (θ t)) (ha0.comp hθ.tendsto_atTop)
      (hweakOrig.comp hθ.tendsto_atTop) hweakScaled hu hρ hmassOrig
      (fun t => hc (θ t)) (hcapacity.comp hθ.tendsto_atTop) (T ∘ θ)
      (fun t y hy => hT (θ t) y hy) (fun t => hgood (θ t)) hK hKpos hv hq
      (Filter.Eventually.of_forall fun t => hmass (ψ t))

end FCAppendix.PayOnce.AnalyticalRareSuccess
