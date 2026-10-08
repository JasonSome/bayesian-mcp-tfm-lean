import FCAppendix.PayOnce.KernelLawConvergence
import FCAppendix.PayOnce.RareSuccessCoverage
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Constructions.Pi

namespace FCAppendix.PayOnce.CompactKernelRareSuccess
open MeasureTheory ProbabilityTheory Filter Topology Set Real
open FCAppendix.CommonList FCAppendix.PayOnce.KernelTailEvent
open FCAppendix.PayOnce.KernelLawConvergence

theorem compactKernel_antitone_price {n : ℕ} (hn : 2 ≤ n) {L T : ℝ}
    (hL : 0 < L) (hT : 0 < T) (hLT : L ≤ T) (b : ENNReal) :
    compactKernel n b T ≤ compactKernel n b L := by
  by_cases hb : b = ⊤
  · simp [hb]
  · simpa [compactKernel, hb] using kernel_antitone_price hn hL hT hLT (b := b.toReal)

theorem compactKernel_transformed_mono {n : ℕ} (hn : 2 ≤ n) {x δ ε : ℝ}
    (hx : 0 < x) (hδ : 0 ≤ δ) (hδε : δ ≤ ε) (hε : ε ≤ 1) (b : ENNReal) :
    compactKernel n b (x * H n δ) ≤ compactKernel n b (x * H n ε) := by
  by_cases hb : b = ⊤
  · simp [hb]
  · simpa [compactKernel, hb] using transformed_kernel_mono hn hx hδ hδε hε (b := b.toReal)

theorem compactKernel_transformed_strict_mass {n : ℕ} (hn : 2 ≤ n)
    (G : Measure ENNReal) {x δ ε : ℝ} (hx : 0 < x) (hδ : 0 ≤ δ)
    (hδε : δ < ε) (hε : ε ≤ 1) (hsupport : ENNReal.ofReal x ∈ G.support) :
    0 < G {b | compactKernel n b (x * H n δ) < compactKernel n b (x * H n ε)} := by
  have hδ1 := hδε.le.trans hε
  have hε0 := hδ.trans hδε.le
  have hcd := (continuous_compactKernel hn (mul_pos hx (H_pos n (by omega) δ hδ hδ1))).continuousAt (x := ENNReal.ofReal x)
  have hce := (continuous_compactKernel hn (mul_pos hx (H_pos n (by omega) ε hε0 hε))).continuousAt (x := ENNReal.ofReal x)
  have he : compactKernel n (ENNReal.ofReal x) (x * H n δ) <
      compactKernel n (ENNReal.ofReal x) (x * H n ε) := by
    rw [compactKernel_ofReal n hx.le, compactKernel_ofReal n hx.le,
      kernel_at_score hn hx hδ hδ1, kernel_at_score hn hx hε0 hε]
    exact hδε
  have hnear := (hcd.sub hce).eventually_lt_const (show
    compactKernel n (ENNReal.ofReal x) (x * H n δ) -
      compactKernel n (ENNReal.ofReal x) (x * H n ε) < 0 from sub_neg.mpr he)
  apply (Measure.mem_support_iff_forall (ENNReal.ofReal x)).mp hsupport
  exact hnear.mono fun _ hh => sub_neg.mp hh

theorem compactKernel_transformed_cgf_lt {n : ℕ} (hn : 2 ≤ n)
    (G : Measure ENNReal) [IsProbabilityMeasure G] {x δ ε u : ℝ}
    (hx : 0 < x) (hδ : 0 ≤ δ) (hδε : δ < ε) (hε : ε ≤ 1)
    (hsupport : ENNReal.ofReal x ∈ G.support) (hu : u < 0) :
    cgf (fun b => compactKernel n b (x * H n ε)) G u <
      cgf (fun b => compactKernel n b (x * H n δ)) G u := by
  have hLδ : 0 < x * H n δ := mul_pos hx (H_pos n (by omega) δ hδ (hδε.le.trans hε))
  have hLε : 0 < x * H n ε := mul_pos hx (H_pos n (by omega) ε (hδ.trans hδε.le) hε)
  exact StrictCramerComparison.cgf_lt_of_order G
    (continuous_compactKernel hn hLδ).measurable.aemeasurable
    (continuous_compactKernel hn hLε).measurable.aemeasurable
    (.of_forall (compactKernel_bounds hn hLδ)) (.of_forall (compactKernel_bounds hn hLε))
    (.of_forall (compactKernel_transformed_mono hn hx hδ hδε.le hε))
    (compactKernel_transformed_strict_mass hn G hx hδ hδε hε hsupport).ne' hu

theorem essInf_le_value_of_mem_support {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
    {G : Measure Ω} {f : Ω → ℝ} {x : Ω} (hf : ContinuousAt f x)
    (hbound : IsBoundedUnder (· ≥ ·) (ae G) f) (hsupport : x ∈ G.support) :
    essInf f G ≤ f x := by
  by_contra hh
  obtain ⟨a, hxa, ha⟩ := exists_between (lt_of_not_ge hh)
  have hmass : 0 < G {b | f b < a} :=
    (Measure.mem_support_iff_forall x).mp hsupport _ (hf.eventually_lt_const hxa)
  have hfreq : ∃ᵐ b ∂G, f b ≤ a := by
    apply frequently_ae_iff.mpr
    exact ne_of_gt (hmass.trans_le (measure_mono fun b hb => (show f b < a from hb).le))
  exact ha.not_ge (liminf_le_of_frequently_le hfreq hbound)

theorem compactKernel_transformed_essInf_le {n : ℕ} (hn : 2 ≤ n)
    (G : Measure ENNReal) {x δ : ℝ} (hx : 0 < x) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hsupport : ENNReal.ofReal x ∈ G.support) :
    essInf (fun b => compactKernel n b (x * H n δ)) G ≤ δ := by
  have hL : 0 < x * H n δ := mul_pos hx (H_pos n (by omega) δ hδ hδ1)
  have hbound : IsBoundedUnder (· ≥ ·) (ae G) (fun b => compactKernel n b (x * H n δ)) :=
    ⟨0, by
      change ∀ᵐ b ∂G, 0 ≤ compactKernel n b (x * H n δ)
      exact Filter.Eventually.of_forall fun b => (compactKernel_bounds hn hL b).1⟩
  have hh := essInf_le_value_of_mem_support (continuous_compactKernel hn hL).continuousAt hbound hsupport
  rwa [compactKernel_ofReal n hx.le, kernel_at_score hn hx hδ hδ1] at hh

theorem essInf_id_map {Ω : Type*} [MeasurableSpace Ω] (G : Measure Ω)
    {f : Ω → ℝ} (hf : Measurable f) : essInf id (G.map f) = essInf f G := by
  rw [essInf_eq_sSup, essInf_eq_sSup]
  congr 1
  ext a
  change (G.map f) (Iio a) = 0 ↔ G {x | f x < a} = 0
  rw [Measure.map_apply hf measurableSet_Iio]
  rfl

theorem integrable_compactKernel {n : ℕ} (hn : 2 ≤ n)
    (G : Measure ENNReal) [IsProbabilityMeasure G] {L : ℝ} (hL : 0 < L) :
    Integrable (fun b => compactKernel n b L) G :=
  UnitInterval.integrable G _ (continuous_compactKernel hn hL).measurable
    (fun b => (compactKernel_bounds hn hL b).1) (fun b => (compactKernel_bounds hn hL b).2)

theorem demand_gt_of_unique_root {n : ℕ} (hn : 2 ≤ n)
    (G : Measure ENNReal) [IsProbabilityMeasure G] {L ρ x s : ℝ}
    (hL : 0 < L) (hroot : (∫ b, compactKernel n b L ∂G) = ρ)
    (hunique : ∀ T : ℝ, 0 < T → (∫ b, compactKernel n b T ∂G) = ρ → T = L)
    (hx : 0 < x) (hxL : x ≤ L) (hs : 0 < s) (hs1 : s ≤ 1) :
    ρ < ∫ b, compactKernel n b (x * H n s) ∂G := by
  have hH := H_pos n (by omega) s hs.le hs1
  have hscore : 0 < x * H n s := mul_pos hx hH
  have hH1 : H n s < 1 := by
    simpa only [H_zero n (by omega)] using H_strict n hn 0 s hs hs1
  have hscoreL : x * H n s < L := (by nlinarith : x * H n s < x).trans_le hxL
  have hle : ρ ≤ ∫ b, compactKernel n b (x * H n s) ∂G := by
    rw [← hroot]
    exact integral_mono (integrable_compactKernel hn G hL)
      (integrable_compactKernel hn G hscore)
      (compactKernel_antitone_price hn hscore hL hscoreL.le)
  exact lt_of_le_of_ne hle (fun he => hscoreL.ne (hunique _ hscore he.symm))

theorem infinity_mass_le_demand {n : ℕ} (hn : 2 ≤ n)
    (G : Measure ENNReal) [IsProbabilityMeasure G] {L : ℝ} (hL : 0 < L) :
    G.real {⊤} ≤ ∫ b, compactKernel n b L ∂G := by
  have hi : Integrable (({⊤} : Set ENNReal).indicator (fun _ => (1 : ℝ))) G :=
    (integrable_const _).indicator (measurableSet_singleton ⊤)
  have hh := integral_mono hi (integrable_compactKernel hn G hL) (fun b => by
    by_cases hb : b = ⊤
    · simp [hb]
    · rw [indicator_of_notMem (show b ∉ ({⊤} : Set ENNReal) by simpa using hb)]
      exact (compactKernel_bounds hn hL b).1)
  simpa only [integral_indicator (measurableSet_singleton ⊤), setIntegral_const,
    smul_eq_mul, mul_one] using hh

theorem identDistrib_map {Ω : Type*} [MeasurableSpace Ω]
    (G : ProbabilityMeasure Ω) {f : Ω → ℝ} (hf : Measurable f) :
    IdentDistrib f id (G : Measure Ω) (G.map hf.aemeasurable : Measure ℝ) := by
  refine ⟨hf.aemeasurable, measurable_id.aemeasurable, ?_⟩
  rw [Measure.map_id]
  rfl

theorem identDistrib_pi_map {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (G : ProbabilityMeasure Ω) {f : Ω → ℝ} (hf : Measurable f) (i : ι) :
    IdentDistrib (fun b : ι → Ω => f (b i)) id
      (Measure.pi fun _ : ι => (G : Measure Ω)) (G.map hf.aemeasurable : Measure ℝ) := by
  have heval : IdentDistrib (fun b : ι → Ω => b i) id
      (Measure.pi fun _ : ι => (G : Measure Ω)) (G : Measure Ω) := by
    refine ⟨(measurable_pi_apply i).aemeasurable, measurable_id.aemeasurable, ?_⟩
    rw [Measure.map_id]
    exact (measurePreserving_eval (fun _ : ι => (G : Measure Ω)) i).map_eq
  exact (heval.comp hf).trans (identDistrib_map G hf)

theorem exponential_kernel_tail_ratio {n : ℕ} (hn : 2 ≤ n)
    {G : ℕ → ProbabilityMeasure ENNReal} {G₀ : ProbabilityMeasure ENNReal}
    (hweak : Tendsto G atTop (𝓝 G₀)) {x : ℕ → ℝ} {x₀ δ ε ρ : ℝ}
    (hx : ∀ m, 0 < x m) (hx₀ : 0 < x₀) (hxx : Tendsto x atTop (𝓝 x₀))
    (hδ : 0 < δ) (hδε : δ < ε) (hε : ε ≤ 1) (hδρ : δ < ρ)
    (hsupport : ENNReal.ofReal x₀ ∈ (G₀ : Measure ENNReal).support)
    (hdemand : ρ < ∫ b, compactKernel n b (x₀ * H n δ) ∂(G₀ : Measure ENNReal))
    {r s : ℕ → ℝ}
    (hr : Tendsto (fun m => r m / m) atTop (𝓝 ρ))
    (hs : Tendsto (fun m => s m / m) atTop (𝓝 ρ)) :
    ∃ c : ℝ, 0 < c ∧
      (∀ᶠ m in atTop,
        0 < (Measure.pi fun _ : Fin m => (G m : Measure ENNReal)).real
          {b | ∑ i, compactKernel n (b i) (x m * H n δ) ≤ r m}) ∧
      (∀ᶠ m in atTop,
        (Measure.pi fun _ : Fin m => (G m : Measure ENNReal)).real
          {b | ∑ i, compactKernel n (b i) (x m * H n ε) ≤ s m} /
        (Measure.pi fun _ : Fin m => (G m : Measure ENNReal)).real
          {b | ∑ i, compactKernel n (b i) (x m * H n δ) ≤ r m} ≤ exp (-c * m)) := by
  let P := fun m => Measure.pi fun _ : Fin m => (G m : Measure ENNReal)
  let X := fun m (i : Fin m) (b : Fin m → ENNReal) => compactKernel n (b i) (x m * H n δ)
  let Y := fun m (i : Fin m) (b : Fin m → ENNReal) => compactKernel n (b i) (x m * H n ε)
  have hδ1 := hδε.le.trans hε
  have hε0 := hδ.le.trans hδε.le
  have hLX (m : ℕ) : 0 < x m * H n δ := mul_pos (hx m) (H_pos n (by omega) δ hδ.le hδ1)
  have hLY (m : ℕ) : 0 < x m * H n ε := mul_pos (hx m) (H_pos n (by omega) ε hε0 hε)
  have hL₀X : 0 < x₀ * H n δ := mul_pos hx₀ (H_pos n (by omega) δ hδ.le hδ1)
  have hL₀Y : 0 < x₀ * H n ε := mul_pos hx₀ (H_pos n (by omega) ε hε0 hε)
  let νX := fun m => (G m).map (continuous_compactKernel hn (hLX m)).measurable.aemeasurable
  let νY := fun m => (G m).map (continuous_compactKernel hn (hLY m)).measurable.aemeasurable
  let μX := G₀.map (continuous_compactKernel hn hL₀X).measurable.aemeasurable
  let μY := G₀.map (continuous_compactKernel hn hL₀Y).measurable.aemeasurable
  have hX : ∀ m i, Measurable (X m i) := fun m i =>
    (continuous_compactKernel hn (hLX m)).measurable.comp (measurable_pi_apply i)
  have hY : ∀ m i, Measurable (Y m i) := fun m i =>
    (continuous_compactKernel hn (hLY m)).measurable.comp (measurable_pi_apply i)
  have hiX : ∀ m, iIndepFun (X m) (P m) := fun m =>
    iIndepFun_pi fun _ => (continuous_compactKernel hn (hLX m)).measurable.aemeasurable
  have hiY : ∀ m, iIndepFun (Y m) (P m) := fun m =>
    iIndepFun_pi fun _ => (continuous_compactKernel hn (hLY m)).measurable.aemeasurable
  have hbX : ∀ m i, ∀ᵐ b ∂P m, X m i b ∈ Icc (0 : ℝ) 1 :=
    fun m i => .of_forall fun b => compactKernel_bounds hn (hLX m) (b i)
  have hbY : ∀ m i, ∀ᵐ b ∂P m, Y m i b ∈ Icc (0 : ℝ) 1 :=
    fun m i => .of_forall fun b => compactKernel_bounds hn (hLY m) (b i)
  have hlawX : ∀ m i, IdentDistrib (X m i) id (P m) (νX m : Measure ℝ) :=
    fun m i => identDistrib_pi_map (G m) (continuous_compactKernel hn (hLX m)).measurable i
  have hlawY : ∀ m i, IdentDistrib (Y m i) id (P m) (νY m : Measure ℝ) :=
    fun m i => identDistrib_pi_map (G m) (continuous_compactKernel hn (hLY m)).measurable i
  have hwX : Tendsto νX atTop (𝓝 μX) :=
    tendsto_transformed_compactKernel_law hn hweak hx hx₀ hxx hδ.le hδ1
  have hwY : Tendsto νY atTop (𝓝 μY) :=
    tendsto_transformed_compactKernel_law hn hweak hx hx₀ hxx hε0 hε
  have hlo : essInf id (μX : Measure ℝ) < ρ := by
    rw [show (μX : Measure ℝ) = (G₀ : Measure ENNReal).map
      (fun b => compactKernel n b (x₀ * H n δ)) from rfl,
      essInf_id_map _ (continuous_compactKernel hn hL₀X).measurable]
    exact (compactKernel_transformed_essInf_le hn _ hx₀ hδ.le hδ1 hsupport).trans_lt hδρ
  have hmean : ρ < ∫ y, y ∂(μX : Measure ℝ) := by
    have he := (identDistrib_map G₀ (continuous_compactKernel hn hL₀X).measurable).integral_eq
    change (∫ b, compactKernel n b (x₀ * H n δ) ∂(G₀ : Measure ENNReal)) =
      ∫ y, y ∂(μX : Measure ℝ) at he
    rwa [← he]
  have hgap : ∀ u : ℝ, u < 0 → cgf id (μY : Measure ℝ) u < cgf id (μX : Measure ℝ) u := by
    intro u hu
    rw [← BoundedLawConvergence.cgf_eq_of_identDistrib
      (identDistrib_map G₀ (continuous_compactKernel hn hL₀X).measurable),
      ← BoundedLawConvergence.cgf_eq_of_identDistrib
      (identDistrib_map G₀ (continuous_compactKernel hn hL₀Y).measurable)]
    exact compactKernel_transformed_cgf_lt hn _ hx₀ hδ.le hδε hε hsupport hu
  obtain ⟨c, hc, hratiob, _⟩ := StrictCramerComparison.exponential_tail_ratio P P X Y
    hX hY hiX hiY hbX hbY hlawX hlawY hwX hwY hr hs hlo hmean hgap
  have hpos := (TriangularCramer.tendsto_log_tail P X hX hiX hbX hlawX hwX hr hlo hmean).1
  exact ⟨c, hc, hpos, hratiob⟩

end FCAppendix.PayOnce.CompactKernelRareSuccess
