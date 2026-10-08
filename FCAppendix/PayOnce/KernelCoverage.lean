import FCAppendix.PayOnce.CompactKernelRareSuccess

namespace FCAppendix.PayOnce.KernelCoverage
open MeasureTheory ProbabilityTheory Filter Topology Set Real
open FCAppendix.CommonList FCAppendix.PayOnce.KernelTailEvent
open FCAppendix.PayOnce.KernelLawConvergence
open FCAppendix.PayOnce.CompactKernelRareSuccess

theorem focal_tail_iff_compact_rival_sum {ι : Type*} [Fintype ι]
    {n : ℕ} (hn : 2 ≤ n) {b L s c : ℝ} (rival : ι → ENNReal)
    (hb : 0 < b) (hL : 0 < L) (hs : 0 < s) (hs1 : s ≤ 1)
    (hcap : kernel n b L + ∑ j, compactKernel n (rival j) L = c) :
    s ≤ kernel n b L ↔ ∑ j, compactKernel n (rival j) (b * H n s) ≤ c - s := by
  have hscore : 0 < b * H n s := mul_pos hb (H_pos n (by omega) s hs.le hs1)
  constructor
  · intro hsp
    have hprice := (le_kernel_iff hn hb hL hs hs1).mp hsp
    have hsum : (∑ j, compactKernel n (rival j) (b * H n s)) ≤
        ∑ j, compactKernel n (rival j) L :=
      Finset.sum_le_sum fun j _ => compactKernel_antitone_price hn hL hscore hprice (rival j)
    linarith
  · intro hsum
    by_contra h
    have hps := lt_of_not_ge h
    have hprice : b * H n s < L :=
      lt_of_not_ge (fun hle => hps.not_ge ((le_kernel_iff hn hb hL hs hs1).mpr hle))
    have hsum' : (∑ j, compactKernel n (rival j) L) ≤
        ∑ j, compactKernel n (rival j) (b * H n s) :=
      Finset.sum_le_sum fun j _ => compactKernel_antitone_price hn hscore hL hprice.le (rival j)
    linarith

theorem focal_tail_probability_eq {ι : Type*} [Fintype ι]
    {n : ℕ} (hn : 2 ≤ n) (G : Measure (ι → ENNReal))
    {b s c : ℝ} (price : (ι → ENNReal) → ℝ)
    (hb : 0 < b) (hprice : ∀ ω, 0 < price ω) (hs : 0 < s) (hs1 : s ≤ 1)
    (hcap : ∀ᵐ ω ∂G, kernel n b (price ω) + ∑ j, compactKernel n (ω j) (price ω) = c) :
    G.real {ω | s ≤ kernel n b (price ω)} =
      G.real {ω | ∑ j, compactKernel n (ω j) (b * H n s) ≤ c - s} := by
  apply congrArg ENNReal.toReal
  apply measure_congr
  filter_upwards [hcap] with ω hω
  exact propext (focal_tail_iff_compact_rival_sum hn ω hb (hprice ω) hs hs1 hω)

theorem tendsto_capacity_sub_div {c : ℕ → ℝ} {ρ : ℝ}
    (hc : Tendsto (fun m => c m / m) atTop (𝓝 ρ)) (s : ℝ) :
    Tendsto (fun m => (c m - s) / m) atTop (𝓝 ρ) := by
  simpa only [sub_div, sub_zero] using hc.sub (tendsto_const_div_atTop_nhds_zero_nat s)

theorem exponential_tail_over_coverage {n : ℕ} (hn : 2 ≤ n)
    {G : ℕ → ProbabilityMeasure ENNReal} {G₀ : ProbabilityMeasure ENNReal}
    (hweak : Tendsto G atTop (𝓝 G₀)) {x : ℕ → ℝ} {x₀ δ ε ρ : ℝ}
    (hx : ∀ m, 0 < x m) (hx₀ : 0 < x₀) (hxx : Tendsto x atTop (𝓝 x₀))
    (hδ : 0 < δ) (hδε : δ < ε) (hε : ε ≤ 1) (hδρ : δ < ρ)
    (hsupport : ENNReal.ofReal x₀ ∈ (G₀ : Measure ENNReal).support)
    (hdemand : ρ < ∫ b, compactKernel n b (x₀ * H n δ) ∂(G₀ : Measure ENNReal))
    {c : ℕ → ℝ} (hc : Tendsto (fun m => c m / m) atTop (𝓝 ρ))
    (price : ∀ m, (Fin m → ENNReal) → ℝ) (hprice : ∀ m ω, 0 < price m ω)
    (hp : ∀ m, Measurable (fun ω => kernel n (x m) (price m ω)))
    (hcap : ∀ m, ∀ᵐ ω ∂(Measure.pi fun _ : Fin m => (G m : Measure ENNReal)),
      kernel n (x m) (price m ω) + ∑ j, compactKernel n (ω j) (price m ω) = c m) :
    ∃ a : ℝ, 0 < a ∧
      (∀ᶠ m in atTop,
        0 < (∫ ω, success n (kernel n (x m) (price m ω))
          ∂(Measure.pi fun _ : Fin m => (G m : Measure ENNReal))) ∧
        (Measure.pi fun _ : Fin m => (G m : Measure ENNReal)).real
          {ω | ε ≤ kernel n (x m) (price m ω)} /
        (∫ ω, success n (kernel n (x m) (price m ω))
          ∂(Measure.pi fun _ : Fin m => (G m : Measure ENNReal))) ≤ exp (-a * m) / success n δ) ∧
      Tendsto (fun m =>
        (Measure.pi fun _ : Fin m => (G m : Measure ENNReal)).real
          {ω | ε ≤ kernel n (x m) (price m ω)} /
        (∫ ω, success n (kernel n (x m) (price m ω))
          ∂(Measure.pi fun _ : Fin m => (G m : Measure ENNReal)))) atTop (𝓝 0) := by
  let P := fun m => Measure.pi fun _ : Fin m => (G m : Measure ENNReal)
  let p := fun m (ω : Fin m → ENNReal) => kernel n (x m) (price m ω)
  have hδ1 := hδε.le.trans hε
  have hε0 := hδ.trans hδε
  have hd (m : ℕ) : (P m).real {ω | δ ≤ p m ω} =
      (P m).real {ω | ∑ j, compactKernel n (ω j) (x m * H n δ) ≤ c m - δ} :=
    focal_tail_probability_eq hn (P m) (price m) (hx m) (hprice m) hδ hδ1 (hcap m)
  have he (m : ℕ) : (P m).real {ω | ε ≤ p m ω} =
      (P m).real {ω | ∑ j, compactKernel n (ω j) (x m * H n ε) ≤ c m - ε} :=
    focal_tail_probability_eq hn (P m) (price m) (hx m) (hprice m) hε0 hε (hcap m)
  obtain ⟨a, ha, hpos, hratio⟩ := exponential_kernel_tail_ratio hn hweak hx hx₀ hxx
    hδ hδε hε hδρ hsupport hdemand (tendsto_capacity_sub_div hc δ) (tendsto_capacity_sub_div hc ε)
  have htpos : ∀ᶠ m in atTop, 0 < (P m).real {ω | δ ≤ p m ω} := by
    filter_upwards [hpos] with m hm
    rw [hd]
    exact hm
  have hratiop : ∀ᶠ m in atTop,
      (P m).real {ω | ε ≤ p m ω} / (P m).real {ω | δ ≤ p m ω} ≤ exp (-a * m) := by
    filter_upwards [hratio] with m hm
    rw [he, hd]
    exact hm
  have hbound : ∀ m ω, p m ω ∈ Icc (0 : ℝ) 1 :=
    fun m ω => kernel_bounds hn (hprice m ω) (x m)
  exact ⟨a, ha, RareSuccessCoverage.tail_ratio_to_coverage P (by omega) p hp hbound
    hδ hδ1 ha htpos hratiop⟩

end FCAppendix.PayOnce.KernelCoverage
