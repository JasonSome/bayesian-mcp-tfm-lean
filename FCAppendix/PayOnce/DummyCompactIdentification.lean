import FCAppendix.PayOnce.BidFormula
import FCAppendix.PayOnce.DummyRareSurplusMass
import FCAppendix.PayOnce.DummyServedIdentification

namespace FCAppendix.PayOnce.DummyRareSuccess
open MeasureTheory ProbabilityTheory Filter Topology Set CommonList
open DummyKernel CompactifiedBidLaws CompactKernelRareSuccess VanishingBidIC

theorem tendsto_compact_identification_defect_zero
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
    {a z : ℝ} (ha : L < a) (haz : a < z) (hz : z < (n:ℝ)*L)
    (hwin : 0 < (G₀ : Measure ENNReal) (Ioo (ENNReal.ofReal a) (ENNReal.ofReal z)))
    (T : ℕ → Set ℝ)
    (hgood : ∀ t, ∀ᵐ y ∂P t, 0 < b t y →
      b t y ∈ regularSupportedSet (ι := Fin (N t)) n (c t) (G t : Measure ℝ) (T t) ∧
      ∀ u ∈ T t, (w t y-u)*coverage n (c t) hn
          (Measure.pi (fun _ : Fin (N t) => (G t : Measure ℝ))) u ≤
        (w t y-b t y)*coverage n (c t) hn
          (Measure.pi (fun _ : Fin (N t) => (G t : Measure ℝ))) (b t y))
    (f : ℝ × ℝ → ℝ) (hf : Continuous f)
    (hgraph : ∀ u : ℝ, 0 ≤ u → f (u,Limit.bidStar n L u) = 0)
    {ε δ R : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    Tendsto (fun t => P t {y | δ ≤ f (w t y,b t y) ∧
      w t y ∈ Icc (0:ℝ) R ∧ b t y ∈ Icc ε R}) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro r hr
    exact (not_lt_of_ge bot_le hr).elim
  · intro q hq
    by_contra hnot
    have hfreq : ∃ᶠ t in atTop, q ≤ P t {y | δ ≤ f (w t y,b t y) ∧
        w t y ∈ Icc (0:ℝ) R ∧ b t y ∈ Icc ε R} := by
      simpa only [not_lt] using not_eventually.mp hnot
    obtain ⟨φ,hφ,hmass⟩ := extraction_of_frequently_atTop hfreq
    have hm t : (scaledLaw (G (φ t)) 1 : Measure ENNReal) =
        (P (φ t)).map (fun y => ENNReal.ofReal (b (φ t) y)) := by
      change (G (φ t) : Measure ℝ).map (fun y => ENNReal.ofReal (y/1)) = _
      simp only [div_one]
      rw [hmap,Measure.map_map ENNReal.measurable_ofReal (hb (φ t))]
      rfl
    obtain ⟨ψ,hψ,y,hy,x₀,hx,hsupp,hconv⟩ := exists_supported_window_subsequence (K := Icc ε R)
      (fun t => P (φ t)) (fun t => b (φ t)) (fun t => hb (φ t))
      (fun t => scaledLaw (G (φ t)) 1) G₀ hm (hweak.comp hφ.tendsto_atTop) isCompact_Icc
      (fun t y => 0 < b (φ t) y → b (φ t) y ∈ regularSupportedSet (ι := Fin (N (φ t))) n (c (φ t))
          (G (φ t) : Measure ℝ) (T (φ t)) ∧
        ∀ u ∈ T (φ t), (w (φ t) y-u)*coverage n (c (φ t)) hn
            (Measure.pi (fun _ : Fin (N (φ t)) => (G (φ t) : Measure ℝ))) u ≤
          (w (φ t) y-b (φ t) y)*coverage n (c (φ t)) hn
            (Measure.pi (fun _ : Fin (N (φ t)) => (G (φ t) : Measure ℝ))) (b (φ t) y))
      (fun t y => δ ≤ f (w (φ t) y,b (φ t) y) ∧ w (φ t) y ∈ Icc (0:ℝ) R)
      (fun t => hgood (φ t)) hq (Eventually.of_forall fun t => by
        convert hmass t using 1
        congr 1
        ext y
        simp only [mem_setOf_eq,and_assoc])
    obtain ⟨w₀,hw₀,χ,hχ,hwconv⟩ := isCompact_Icc.isSeqCompact (fun t => (hy t).2.1.2)
    let θ := φ ∘ ψ ∘ χ
    have hθ : StrictMono θ := hφ.comp (hψ.comp hχ)
    have hxconv := hconv.comp hχ.tendsto_atTop
    have hchosen t := (hy (χ t)).1 (hε.trans_le (hy (χ t)).2.2.1)
    have hident : x₀ = Limit.bidStar n L w₀ := by
      by_cases hexcluded : x₀ ≤ L
      · have hdemand s (hs : 0 < s) (hs1 : s ≤ 1) :
          ρ < ∫ v, KernelLawConvergence.compactKernel n v (x₀*H n s) ∂(G₀ : Measure ENNReal) :=
          demand_gt_of_unique_root hn (G₀ : Measure ENNReal) hL hroot hunique
            (hε.trans_le hx.1) hexcluded hs hs1
        have hsurplus := (surplus_tendsto_zero_of_supported_IC_rows (N ∘ θ)
          (fun t => hNpos (θ t)) (hN.comp hθ.tendsto_atTop) hn (G ∘ θ) (fun t => hpos (θ t))
          (hweak.comp hθ.tendsto_atTop)
          (fun t => (hchosen t).1) (hε.trans_le hx.1) hxconv hρ hsupp hdemand
          (hcapacity.comp hθ.tendsto_atTop) (fun t => (hchosen t).2)).2
        have hwx : w₀-x₀ = 0 := tendsto_nhds_unique (hwconv.sub hxconv) hsurplus
        have hweq : w₀ = x₀ := by linarith
        rw [hweq,Limit.bidStar_of_le hexcluded,max_eq_left (hε.trans_le hx.1).le]
      · have hh := served_formulas_of_supported_IC_limit (N ∘ θ)
          (fun t => hNpos (θ t)) (hN.comp hθ.tendsto_atTop) hn (G ∘ θ) (fun t => hpos (θ t))
          (hweak.comp hθ.tendsto_atTop) hL hroot hunique
          (hcapacity.comp hθ.tendsto_atTop) ha haz hz hwin
          (fun t => (hchosen t).1) (lt_of_not_ge hexcluded) hxconv hwconv
          (fun t => (hchosen t).2)
        rw [Limit.bidStar_of_lt hh.1]
        exact hh.2.2.1
    have hfconv : Tendsto (fun t => f (w (θ t) (y (χ t)),b (θ t) (y (χ t)))) atTop (𝓝 0) := by
      have hh := hf.continuousAt.tendsto.comp (hwconv.prodMk_nhds hxconv)
      rw [hident,hgraph w₀ hw₀.1] at hh
      exact hh
    exact hδ.not_ge (ge_of_tendsto hfconv (Eventually.of_forall fun t => (hy (χ t)).2.1.1))

end FCAppendix.PayOnce.DummyRareSuccess
