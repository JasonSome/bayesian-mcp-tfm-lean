import FCAppendix.PayOnce.DummyRareSuccessRows
import FCAppendix.PayOnce.DummyScaling

noncomputable section
namespace FCAppendix.PayOnce.DummyRareSuccess
open MeasureTheory ProbabilityTheory Filter Topology Set Real
open CommonList DummyKernel KernelLawConvergence CompactKernelRareSuccess
open CompactifiedBidLaws BidScaling
open AnalyticalKernel (rescaledRealLaw compactified_rescaledRealLaw)

theorem value_tendsto_zero_of_vanishing_scale
    (N : ℕ → ℕ) (hNpos : ∀ m, 0 < N m) (hN : Tendsto N atTop atTop)
    {n : ℕ} (hn : 2 ≤ n)
    (G : ℕ → ProbabilityMeasure ℝ) (hpos : ∀ m, ∀ᵐ b ∂(G m : Measure ℝ), 0 ≤ b)
    (a : ℕ → ℝ) (ha : ∀ m, 0 < a m) (ha0 : Tendsto a atTop (𝓝 0))
    {Gorig Gscaled : ProbabilityMeasure ENNReal}
    (hweakOrig : Tendsto (fun m => scaledLaw (G m) 1) atTop (𝓝 Gorig))
    (hweakScaled : Tendsto (fun m => scaledLaw (G m) (a m)) atTop (𝓝 Gscaled))
    {u ρ : ℝ} (hu : 0 < u) (hρ : 0 < ρ)
    (hmass : ρ < (Gorig : Measure ENNReal).real (Ioi (ENNReal.ofReal u)))
    {c : ℕ → ℕ}
    (hcapacity : Tendsto (fun m => (c m : ℝ) / N m) atTop (𝓝 ρ))
    (T : ℕ → Set ℝ)
    (x w : ℕ → ℝ) {x₀ : ℝ} (hx₀ : 0 < x₀)
    (hxx : Tendsto (fun m => x m / a m) atTop (𝓝 x₀))
    (hsupport : ENNReal.ofReal x₀ ∈ (Gscaled : Measure ENNReal).support)
    (hgood : ∀ m, x m / a m ∈ regularSupportedSet (ι := Fin (N m)) n (c m)
      (rescaledRealLaw (G m) (a m) : Measure ℝ) ((fun b => b / a m) '' T m))
    (hIC : ∀ m y, y ∈ T m →
      (w m-y) * coverage n (c m) hn
        (Measure.pi (fun _ : Fin (N m) => (G m : Measure ℝ))) y ≤
      (w m-x m) * coverage n (c m) hn
        (Measure.pi (fun _ : Fin (N m) => (G m : Measure ℝ))) (x m)) :
    Tendsto w atTop (𝓝 0) := by
  have hInf := scaled_infinity_mass_gt_capacity ha ha0 hweakOrig hweakScaled hu hρ.le hmass
  have hweak : Tendsto (fun m => scaledLaw (rescaledRealLaw (G m) (a m)) 1)
      atTop (𝓝 Gscaled) := by
    simpa only [compactified_rescaledRealLaw] using hweakScaled
  have hdemand (s : ℝ) (hs : 0 < s) (hs1 : s ≤ 1) :
      ρ < ∫ b, compactKernel n b (x₀ * H n s) ∂(Gscaled : Measure ENNReal) :=
    hInf.trans_le (infinity_mass_le_demand hn _
      (mul_pos hx₀ (H_pos n (by omega) s hs.le hs1)))
  have hscaledIC (m : ℕ) (y : ℝ) (hy : y ∈ (fun b => b / a m) '' T m) :
      (w m / a m - y) * coverage n (c m) hn
        (Measure.pi (fun _ : Fin (N m) => (rescaledRealLaw (G m) (a m) : Measure ℝ))) y ≤
      (w m / a m - x m / a m) * coverage n (c m) hn
        (Measure.pi (fun _ : Fin (N m) => (rescaledRealLaw (G m) (a m) : Measure ℝ)))
          (x m / a m) := by
    obtain ⟨b, hb, rfl⟩ := hy
    exact scaled_coverage_IC hn (G m) (ha m) (hIC m b hb)
  have hs := (surplus_tendsto_zero_of_supported_IC_rows N hNpos hN hn
    (fun m => rescaledRealLaw (G m) (a m))
    (fun m => ae_nonneg_rescaledRealLaw (G m) (ha m) (hpos m)) hweak hgood hx₀ hxx
    hρ hsupport hdemand hcapacity hscaledIC).2
  have hw : Tendsto (fun m => w m / a m) atTop (𝓝 x₀) := by
    have hh := hs.add hxx
    simpa only [sub_add_cancel, zero_add] using hh
  have hmul := ha0.mul hw
  simp only [zero_mul] at hmul
  apply hmul.congr
  intro m
  exact mul_div_cancel₀ (w m) (ha m).ne'

end FCAppendix.PayOnce.DummyRareSuccess
