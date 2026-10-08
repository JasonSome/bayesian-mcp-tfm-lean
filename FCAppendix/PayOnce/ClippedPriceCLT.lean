import FCAppendix.Probability.ClippedSubGaussianMoments
import FCAppendix.PayOnce.InactivePriceCLT

namespace FCAppendix.Probability
open MeasureTheory ProbabilityTheory Set

theorem clipToInterval_eq_of_mem {ell u x : ℝ} (hx : x ∈ Icc ell u) :
    clipToInterval ell u x = x := by
  rw [clipToInterval,min_eq_right hx.2,max_eq_right hx.1]

theorem standardized_clipToInterval_le_iff {ell u center s z x : ℝ}
    (hs : 0 < s) (hT : center+s*z ∈ Ioo ell u) :
    (clipToInterval ell u x-center)/s ≤ z ↔ (x-center)/s ≤ z := by
  rw [div_le_iff₀ hs,div_le_iff₀ hs]
  have hc := clipToInterval_le_iff (x := x) hT
  constructor <;> intro hx
  · have hx' : clipToInterval ell u x ≤ center+s*z := by linarith
    have := hc.mp hx'
    linarith
  · have hx' : x ≤ center+s*z := by linarith
    have := hc.mpr hx'
    linarith

theorem cdf_standardized_clipToInterval_eq
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX : Measurable X) {ell u center s z : ℝ}
    (hs : 0 < s) (hT : center+s*z ∈ Ioo ell u) :
    cdf (μ.map (fun ω => (clipToInterval ell u (X ω)-center)/s)) z =
      cdf (μ.map (fun ω => (X ω-center)/s)) z := by
  have hm : Measurable (fun ω => (clipToInterval ell u (X ω)-center)/s) :=
    (((measurable_clipToInterval ell u).comp hX).sub_const center).div_const s
  have hm' := (hX.sub_const center).div_const s
  haveI hI : IsProbabilityMeasure (μ.map (fun ω => (clipToInterval ell u (X ω)-center)/s)) :=
    Measure.isProbabilityMeasure_map hm.aemeasurable
  haveI hI' : IsProbabilityMeasure (μ.map (fun ω => (X ω-center)/s)) :=
    Measure.isProbabilityMeasure_map hm'.aemeasurable
  rw [cdf_eq_real,cdf_eq_real,map_measureReal_apply hm measurableSet_Iic,
    map_measureReal_apply hm' measurableSet_Iic]
  congr 1
  ext ω
  exact standardized_clipToInterval_le_iff hs hT

end FCAppendix.Probability

namespace FCAppendix.PayOnce.DummyKernel
open MeasureTheory ProbabilityTheory Set
variable {N M n c : ℕ}

noncomputable def clippedFocalPrice (n c : ℕ) (hn : 2 ≤ n) (ell u b : ℝ)
    (r : Fin N → ℝ) : ℝ :=
  Probability.clipToInterval ell u (focalPrice n c hn b r)

noncomputable def clippedProfilePrice (n c : ℕ) (hn : 2 ≤ n) (ell u : ℝ)
    (r : Fin M → ℝ) : ℝ :=
  Probability.clipToInterval ell u (sampleProfilePrice n c hn r)

theorem measurable_clippedFocalPrice (hn : 2 ≤ n) (ell u b : ℝ) :
    Measurable (clippedFocalPrice (N := N) n c hn ell u b) :=
  (Probability.measurable_clipToInterval ell u).comp (measurable_focalPrice hn b)

theorem measurable_clippedFocalPrice_joint (hn : 2 ≤ n) (ell u : ℝ) :
    Measurable (fun z : ℝ × (Fin N → ℝ) => clippedFocalPrice n c hn ell u z.1 z.2) :=
  (Probability.measurable_clipToInterval ell u).comp (measurable_focalPrice_joint hn)

theorem measurable_clippedProfilePrice (hn : 2 ≤ n) (ell u : ℝ) :
    Measurable (clippedProfilePrice (M := M) n c hn ell u) :=
  (Probability.measurable_clipToInterval ell u).comp (measurable_sampleProfilePrice hn)

theorem clippedFocalPrice_eq_of_mem (hn : 2 ≤ n) {ell u b : ℝ} (r : Fin N → ℝ)
    (hr : focalPrice n c hn b r ∈ Icc ell u) :
    clippedFocalPrice n c hn ell u b r = focalPrice n c hn b r :=
  Probability.clipToInterval_eq_of_mem hr

theorem clippedProfilePrice_eq_of_mem (hn : 2 ≤ n) {ell u : ℝ} (r : Fin M → ℝ)
    (hr : sampleProfilePrice n c hn r ∈ Icc ell u) :
    clippedProfilePrice n c hn ell u r = sampleProfilePrice n c hn r :=
  Probability.clipToInterval_eq_of_mem hr

theorem cdf_standardized_clippedFocalPrice_eq (hn : 2 ≤ n)
    (μ : Measure (Fin N → ℝ)) [IsProbabilityMeasure μ] (b : ℝ)
    {ell u center s z : ℝ} (hs : 0 < s) (hT : center+s*z ∈ Ioo ell u) :
    cdf (μ.map (fun r => (clippedFocalPrice n c hn ell u b r-center)/s)) z =
      μ.real {r | (focalPrice n c hn b r-center)/s ≤ z} := by
  rw [show (fun r => (clippedFocalPrice n c hn ell u b r-center)/s) =
    (fun r => (Probability.clipToInterval ell u (focalPrice n c hn b r)-center)/s) from rfl,
    Probability.cdf_standardized_clipToInterval_eq μ (measurable_focalPrice hn b) hs hT]
  have hm := ((measurable_focalPrice (N := N) (c := c) hn b).sub_const center).div_const s
  haveI := Measure.isProbabilityMeasure_map (μ := μ) hm.aemeasurable
  rw [cdf_eq_real,map_measureReal_apply hm measurableSet_Iic]
  rfl

theorem cdf_standardized_clippedProfilePrice_eq (hn : 2 ≤ n)
    (μ : Measure (Fin M → ℝ)) [IsProbabilityMeasure μ]
    {ell u center s z : ℝ} (hs : 0 < s) (hT : center+s*z ∈ Ioo ell u) :
    cdf (μ.map (fun r => (clippedProfilePrice n c hn ell u r-center)/s)) z =
      cdf (μ.map (fun r => (sampleProfilePrice n c hn r-center)/s)) z :=
  Probability.cdf_standardized_clipToInterval_eq μ (measurable_sampleProfilePrice hn) hs hT

end FCAppendix.PayOnce.DummyKernel

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology CommonList
open PayOnce PayOnce.CompactifiedBidLaws PayOnce.DummyKernel
variable {N M C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem payOnce_inactive_clipped_focal_price_gaussian_uniform
    (Γ : ∀ t, FiniteGame (N t+1) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions (fun t => N t+1) C Γ B F g ρ)
    (hlocal : GaussianParameters.LocalFullSupport (F.map (fun v => max (v-g) 0))
      (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ))
    (ell u : ℝ) (hell : ell < Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ)
    (hu : Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ < u) (x : ℝ) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ t in atTop, ∀ b : ℝ, 0 < b →
      |cdf ((Measure.pi (fun _ : Fin (N t) => (BidScaling.realBidLaw (Γ t) : Measure ℝ))).map
        (fun r => (clippedFocalPrice (k+1) (C t) (by have hk := h.proposers_two; omega) ell u b r -
          KernelDemand.populationPrice (k+1) (bidLaw (Γ t) : Measure ENNReal)
            ((C t:ℝ)/(N t+1:ℕ)))/
          inactiveGaussianScale (fun t => N t+1) F (k+1) g ρ t)) x -
        cdf (gaussianReal 0 1) x| < ε := by
  have hk := h.proposers_two
  have hinside := (payOnce_inactive_gaussian_price_tendsto Γ B F g ρ h x).eventually
    (Ioo_mem_nhds hell hu)
  intro ε hε
  filter_upwards [hinside,payOnce_inactive_focal_price_gaussian_uniform Γ B F g ρ h hlocal x ε hε]
    with t ht hc b hb
  have hs := payOnce_inactive_gaussian_scale_pos Γ B F g ρ h hlocal (t := t) (by omega)
  rw [cdf_standardized_clippedFocalPrice_eq (by omega) _ b hs ht]
  exact hc b hb

private theorem payOnce_inactive_clipped_focal_price_gaussian_uniform_population_of_pos
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ)
    (hlocal : GaussianParameters.LocalFullSupport (F.map (fun v => max (v-g) 0))
      (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ))
    (ell u : ℝ) (hell : ell < Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ)
    (hu : Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ < u) (x : ℝ) (hpos : ∀ t, 0 < M t) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ t in atTop, ∀ b : ℝ, 0 < b →
      |cdf ((Measure.pi (fun _ : Fin (M t-1) => (BidScaling.realBidLaw (Γ t) : Measure ℝ))).map
        (fun r => (clippedFocalPrice (k+1) (C t) (by have hk := h.proposers_two; omega) ell u b r -
          KernelDemand.populationPrice (k+1) (bidLaw (Γ t) : Measure ENNReal)
            ((C t:ℝ)/(M t)))/
          inactiveGaussianScale M F (k+1) g ρ t)) x -
        cdf (gaussianReal 0 1) x| < ε := by
  obtain ⟨N,hN,rfl⟩ := exists_successor_population h.population_grows hpos
  exact payOnce_inactive_clipped_focal_price_gaussian_uniform Γ B F g ρ h hlocal ell u hell hu x

theorem payOnce_inactive_clipped_focal_price_gaussian_uniform_population
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ)
    (hlocal : GaussianParameters.LocalFullSupport (F.map (fun v => max (v-g) 0))
      (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ))
    (ell u : ℝ) (hell : ell < Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ)
    (hu : Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ < u) (x : ℝ) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ t in atTop, ∀ b : ℝ, 0 < b →
      |cdf ((Measure.pi (fun _ : Fin (M t-1) => (BidScaling.realBidLaw (Γ t) : Measure ℝ))).map
        (fun r => (clippedFocalPrice (k+1) (C t) (by have hk := h.proposers_two; omega) ell u b r -
          KernelDemand.populationPrice (k+1) (bidLaw (Γ t) : Measure ENNReal)
            ((C t:ℝ)/(M t)))/
          inactiveGaussianScale M F (k+1) g ρ t)) x -
        cdf (gaussianReal 0 1) x| < ε := by
  obtain ⟨T,hT⟩ := eventually_atTop.mp (h.population_grows.eventually_gt_atTop 0)
  have hh := payOnce_inactive_clipped_focal_price_gaussian_uniform_population_of_pos
    (fun t => Γ (t+T)) (fun t => B (t+T)) F g ρ
    (h.along (fun t => t+T) (tendsto_add_atTop_nat T)) hlocal ell u hell hu x
    (fun t => hT (t+T) (by omega))
  intro ε hε
  obtain ⟨A,hA⟩ := eventually_atTop.mp (hh ε hε)
  apply eventually_atTop.mpr
  refine ⟨A+T,fun t ht => ?_⟩
  have he : t-T+T = t := Nat.sub_add_cancel (by omega)
  have ha := hA (t-T) (by omega)
  rw [← he]
  exact ha

theorem payOnce_inactive_clipped_profile_price_gaussian_cdf
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ)
    (hlocal : GaussianParameters.LocalFullSupport (F.map (fun v => max (v-g) 0))
      (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ))
    (ell u : ℝ) (hell : ell < Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ)
    (hu : Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ < u) (x : ℝ) :
    Tendsto (fun t => cdf ((Measure.pi (fun _ : Fin (M t) =>
      (BidScaling.realBidLaw (Γ t) : Measure ℝ))).map (fun r =>
        (clippedProfilePrice (k+1) (C t) (by have hk := h.proposers_two; omega) ell u r -
          KernelDemand.populationPrice (k+1) (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t)))/
        inactiveGaussianScale M F (k+1) g ρ t)) x) atTop (𝓝 (cdf (gaussianReal 0 1) x)) := by
  have hk := h.proposers_two
  have hinside := (payOnce_inactive_gaussian_price_tendsto Γ B F g ρ h x).eventually
    (Ioo_mem_nhds hell hu)
  apply (payOnce_inactive_profile_price_gaussian_cdf Γ B F g ρ h hlocal x).congr'
  filter_upwards [hinside,h.population_grows.eventually_gt_atTop 0] with t ht hm
  exact (cdf_standardized_clippedProfilePrice_eq (by omega) _
    (payOnce_inactive_gaussian_scale_pos Γ B F g ρ h hlocal hm) ht).symm

end FCAppendix.Bayes
