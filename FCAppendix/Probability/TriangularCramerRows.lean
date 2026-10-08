import FCAppendix.Probability.StrictCramerComparison

namespace FCAppendix.TriangularCramerBounds
open MeasureTheory ProbabilityTheory Filter Topology Set Real
open FCAppendix.ExponentialTilt FCAppendix.BoundedLawConvergence

variable {Ω : ℕ → Type*} [∀ m, MeasurableSpace (Ω m)]
    (N : ℕ → ℕ) (hNpos : ∀ m, 0 < N m) (hN : Tendsto N atTop atTop)
    (P : ∀ m, Measure (Ω m)) [∀ m, IsProbabilityMeasure (P m)]
    (Y : ∀ m, Fin (N m) → Ω m → ℝ)
    {ν : ℕ → ProbabilityMeasure ℝ} {μ : ProbabilityMeasure ℝ}

def tailProbability_rows (r : ℕ → ℝ) (m : ℕ) : ℝ :=
  (P m).real {ω | rowSum (Y m) ω ≤ r m}

omit [∀ m, IsProbabilityMeasure (P m)] in

theorem coordinate_bounded_rows
    (hν : ∀ m, ∀ᵐ x ∂(ν m : Measure ℝ), x ∈ Icc (0 : ℝ) 1)
    (hlaw : ∀ m i, IdentDistrib (Y m i) id (P m) (ν m : Measure ℝ))
    (m : ℕ) (i : Fin (N m)) : ∀ᵐ ω ∂P m, Y m i ω ∈ Icc (0 : ℝ) 1 :=
  (hlaw m i).symm.ae_mem_snd measurableSet_Icc (hν m)

theorem coordinate_tilted_mean_rows
    (hν : ∀ m, ∀ᵐ x ∂(ν m : Measure ℝ), x ∈ Icc (0 : ℝ) 1)
    (hlaw : ∀ m i, IdentDistrib (Y m i) id (P m) (ν m : Measure ℝ))
    (m : ℕ) (i : Fin (N m)) (u : ℝ) :
    (∫ ω, Y m i ω ∂((P m).tilted (fun ω => u * Y m i ω))) =
      ∫ x, x ∂((ν m : Measure ℝ).tilted (fun x => u * x)) := by
  apply tilted_mean_eq_of_identDistrib (hlaw m i)
  · rw [integrableExpSet_eq_univ_of_bounded (P m) (hlaw m i).aemeasurable_fst
      (coordinate_bounded_rows N P Y hν hlaw m i), interior_univ]
    trivial
  · rw [integrableExpSet_eq_univ_of_bounded (ν m : Measure ℝ)
      measurable_id.aemeasurable (hν m), interior_univ]
    trivial

include hNpos hN in

theorem eventually_log_lower_of_tilt_rows
    (hY : ∀ m i, Measurable (Y m i)) (hind : ∀ m, iIndepFun (Y m) (P m))
    (hν : ∀ m, ∀ᵐ x ∂(ν m : Measure ℝ), x ∈ Icc (0 : ℝ) 1)
    (hμ : ∀ᵐ x ∂(μ : Measure ℝ), x ∈ Icc (0 : ℝ) 1)
    (hlaw : ∀ m i, IdentDistrib (Y m i) id (P m) (ν m : Measure ℝ))
    (hweak : Tendsto ν atTop (𝓝 μ)) {r : ℕ → ℝ} {ρ u ε c : ℝ}
    (hr : Tendsto (fun m => r m / (N m)) atTop (𝓝 ρ))
    (hu : u ≤ 0) (hε : 0 < ε)
    (hz : (∫ x, x ∂((μ : Measure ℝ).tilted (fun x => u * x))) + ε < ρ)
    (hc : c < cgf id (μ : Measure ℝ) u -
      u * ((∫ x, x ∂((μ : Measure ℝ).tilted (fun x => u * x))) - ε)) :
    ∀ᶠ m in atTop, 0 < tailProbability_rows N P Y r m ∧
      c ≤ log (tailProbability_rows N P Y r m) / (N m) := by
  let z : ℕ → ℝ := fun m => ∫ x, x ∂((ν m : Measure ℝ).tilted (fun x => u * x))
  have hzlim := tendsto_tilted_mean hν hμ hweak u
  have hgap := (hzlim.add_const ε).sub hr
  have hthreshold : ∀ᶠ m in atTop, z m + ε ≤ r m / (N m) := by
    filter_upwards [hgap.eventually_lt_const (show
      (∫ x, x ∂((μ : Measure ℝ).tilted (fun x => u * x))) + ε - ρ < 0 by linarith)] with m hm
    change z m + ε - r m / (N m) < 0 at hm
    linarith
  have hmTop : Tendsto (fun m : ℕ => ((N m) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hN
  have hlarge : ∀ᶠ m : ℕ in atTop, 2 ≤ 4 * (N m) * ε ^ 2 := by
    have hh := (hmTop.const_mul_atTop (show 0 < 4 * ε ^ 2 by positivity)).eventually_ge_atTop 2
    filter_upwards [hh] with m hm
    nlinarith
  have hlogzero : Tendsto (fun m : ℕ => log 2 / (N m)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (log 2) |>.comp hN
  have hlower := ((tendsto_cgf hν hμ hweak u).sub
    ((hzlim.sub_const ε).const_mul u)).sub hlogzero
  have hbound : ∀ᶠ m in atTop,
      c < cgf id (ν m : Measure ℝ) u - u * (z m - ε) - log 2 / (N m) := by
    exact hlower.eventually_const_lt (by simpa using hc)
  filter_upwards [hthreshold, hlarge, hbound] with m hth hla hlo
  have hm : (0 : ℝ) < (N m) := Nat.cast_pos.mpr (hNpos m)
  have hf := iid_row_log_lower_bound (r := r m) (P m) (hY m)
    (coordinate_bounded_rows N P Y hν hlaw m) (hind m) (⟨0, hNpos m⟩ : Fin (N m))
    (fun j => (hlaw m j).trans (hlaw m ⟨0, hNpos m⟩).symm) hu hε hla
  rw [coordinate_tilted_mean_rows N P Y hν hlaw] at hf
  have ht : (N m) * (z m + ε) ≤ r m := by
    simpa only [mul_comm] using (le_div_iff₀ hm).mp hth
  have hh := hf ht
  rw [cgf_eq_of_identDistrib (hlaw m ⟨0, hNpos m⟩)] at hh
  exact ⟨hh.1, hlo.le.trans hh.2⟩

include hNpos hN in

theorem eventually_log_lower_rows
    (hY : ∀ m i, Measurable (Y m i)) (hind : ∀ m, iIndepFun (Y m) (P m))
    (hν : ∀ m, ∀ᵐ x ∂(ν m : Measure ℝ), x ∈ Icc (0 : ℝ) 1)
    (hμ : ∀ᵐ x ∂(μ : Measure ℝ), x ∈ Icc (0 : ℝ) 1)
    (hlaw : ∀ m i, IdentDistrib (Y m i) id (P m) (ν m : Measure ℝ))
    (hweak : Tendsto ν atTop (𝓝 μ)) {r : ℕ → ℝ} {ρ u c : ℝ}
    (hr : Tendsto (fun m => r m / (N m)) atTop (𝓝 ρ))
    (hu : u ≤ 0)
    (hz : (∫ x, x ∂((μ : Measure ℝ).tilted (fun x => u * x))) < ρ)
    (hc : c < cgf id (μ : Measure ℝ) u -
      u * (∫ x, x ∂((μ : Measure ℝ).tilted (fun x => u * x)))) :
    ∀ᶠ m in atTop, 0 < tailProbability_rows N P Y r m ∧
      c ≤ log (tailProbability_rows N P Y r m) / (N m) := by
  let z := ∫ x, x ∂((μ : Measure ℝ).tilted (fun x => u * x))
  let a := cgf id (μ : Measure ℝ) u - u * z
  let ε := min ((ρ - z) / 2) ((a - c) / (2 * (|u| + 1)))
  have hd : 0 < 2 * (|u| + 1) := by positivity
  have hε : 0 < ε := lt_min (by dsimp [z]; linarith) (div_pos (sub_pos.mpr hc) hd)
  have hε₁ : ε ≤ (ρ - z) / 2 := min_le_left _ _
  have hε₂ : ε * (2 * (|u| + 1)) ≤ a - c :=
    (le_div_iff₀ hd).mp (min_le_right _ _)
  have huε := mul_le_mul_of_nonneg_right (neg_le_abs u) hε.le
  apply eventually_log_lower_of_tilt_rows N hNpos hN P Y hY hind hν hμ hlaw hweak hr hu hε
  · change z + ε < ρ
    linarith
  · change c < cgf id (μ : Measure ℝ) u - u * (z - ε)
    dsimp [a] at hε₂
    nlinarith

include hNpos in

theorem eventually_log_upper_rows
    (hY : ∀ m i, Measurable (Y m i)) (hind : ∀ m, iIndepFun (Y m) (P m))
    (hν : ∀ m, ∀ᵐ x ∂(ν m : Measure ℝ), x ∈ Icc (0 : ℝ) 1)
    (hμ : ∀ᵐ x ∂(μ : Measure ℝ), x ∈ Icc (0 : ℝ) 1)
    (hlaw : ∀ m i, IdentDistrib (Y m i) id (P m) (ν m : Measure ℝ))
    (hweak : Tendsto ν atTop (𝓝 μ)) {r : ℕ → ℝ} {ρ u c : ℝ}
    (hr : Tendsto (fun m => r m / (N m)) atTop (𝓝 ρ))
    (hpos : ∀ᶠ m in atTop, 0 < tailProbability_rows N P Y r m)
    (hu : u ≤ 0) (hc : cgf id (μ : Measure ℝ) u - u * ρ < c) :
    ∀ᶠ m in atTop, log (tailProbability_rows N P Y r m) / (N m) ≤ c := by
  have hl := (tendsto_cgf hν hμ hweak u).sub (hr.const_mul u)
  filter_upwards [hpos, hl.eventually_lt_const hc] with m hp hm
  have hf := iid_row_log_upper_bound (P m) (hY m)
    (coordinate_bounded_rows N P Y hν hlaw m) (hind m) (⟨0, hNpos m⟩ : Fin (N m))
    (fun j => (hlaw m j).trans (hlaw m ⟨0, hNpos m⟩).symm) hu hp
  rw [cgf_eq_of_identDistrib (hlaw m ⟨0, hNpos m⟩)] at hf
  exact hf.trans hm.le

end FCAppendix.TriangularCramerBounds

namespace FCAppendix.TriangularCramer
open MeasureTheory ProbabilityTheory Filter Topology Set Real
open FCAppendix.ExponentialTilt FCAppendix.TriangularCramerBounds
open FCAppendix.CramerOptimizer

theorem tendsto_log_tail_rows_of_support
    {Ω : ℕ → Type*} [∀ m, MeasurableSpace (Ω m)]
    (N : ℕ → ℕ) (hNpos : ∀ m, 0 < N m) (hN : Tendsto N atTop atTop)
    (P : ∀ m, Measure (Ω m)) [∀ m, IsProbabilityMeasure (P m)]
    (Y : ∀ m, Fin (N m) → Ω m → ℝ)
    (hY : ∀ m i, Measurable (Y m i)) (hind : ∀ m, iIndepFun (Y m) (P m))
    {ν : ℕ → ProbabilityMeasure ℝ} {μ : ProbabilityMeasure ℝ}
    (hν : ∀ m, ∀ᵐ x ∂(ν m : Measure ℝ), x ∈ Icc (0 : ℝ) 1)
    (hμ : ∀ᵐ x ∂(μ : Measure ℝ), x ∈ Icc (0 : ℝ) 1)
    (hlaw : ∀ m i, IdentDistrib (Y m i) id (P m) (ν m : Measure ℝ))
    (hweak : Tendsto ν atTop (𝓝 μ)) {r : ℕ → ℝ} {ρ : ℝ}
    (hr : Tendsto (fun m => r m / (N m)) atTop (𝓝 ρ))
    (hlower : essInf id (μ : Measure ℝ) < ρ)
    (hmean : ρ < ∫ x, x ∂(μ : Measure ℝ)) :
    (∀ᶠ m in atTop, 0 < tailProbability_rows N P Y r m) ∧
    Tendsto (fun m => log (tailProbability_rows N P Y r m) / (N m)) atTop
      (𝓝 (-lowerRate μ ρ)) := by
  have hlo (c : ℝ) (hc : c < -lowerRate μ ρ) :
      ∀ᶠ m in atTop, 0 < tailProbability_rows N P Y r m ∧
        c ≤ log (tailProbability_rows N P Y r m) / (N m) := by
    obtain ⟨u, hu, hz, hcu⟩ := exists_tilt_lower_bound μ hμ hlower hmean hc
    have htilt := integral_tilted_mul_self (mem_interior_all μ hμ u)
    have htilt' : (∫ x, x ∂((μ : Measure ℝ).tilted (fun x => u * x))) =
        deriv (cgf id (μ : Measure ℝ)) u := htilt
    apply eventually_log_lower_rows N hNpos hN P Y hY hind hν hμ hlaw hweak hr hu
    · rwa [htilt']
    · rwa [htilt']
  have hpos : ∀ᶠ m in atTop, 0 < tailProbability_rows N P Y r m :=
    (hlo (-lowerRate μ ρ - 1) (by linarith)).mono fun _ hm => hm.1
  refine ⟨hpos, tendsto_order.mpr ⟨?_, ?_⟩⟩
  · intro c hc
    obtain ⟨d, hcd, hd⟩ := exists_between hc
    exact (hlo d hd).mono fun _ hm => hcd.trans_le hm.2
  · intro c hc
    obtain ⟨d, hd, hdc⟩ := exists_between hc
    obtain ⟨u, hu, hdu⟩ := exists_negative_tilt_of_essInf μ hμ hlower hmean
    have he : cgf id (μ : Measure ℝ) u - u * ρ = -lowerRate μ ρ := by
      rw [lowerRate_eq μ hμ hu.le hdu]
      ring
    have hh := eventually_log_upper_rows N hNpos P Y hY hind hν hμ hlaw hweak hr hpos hu.le
      (he ▸ hd)
    exact hh.mono fun _ hm => hm.trans_lt hdc

theorem tendsto_log_tail_rows
    {Ω : ℕ → Type*} [∀ m, MeasurableSpace (Ω m)]
    (N : ℕ → ℕ) (hNpos : ∀ m, 0 < N m) (hN : Tendsto N atTop atTop)
    (P : ∀ m, Measure (Ω m)) [∀ m, IsProbabilityMeasure (P m)]
    (Y : ∀ m, Fin (N m) → Ω m → ℝ)
    (hY : ∀ m i, Measurable (Y m i)) (hind : ∀ m, iIndepFun (Y m) (P m))
    {ν : ℕ → ProbabilityMeasure ℝ} {μ : ProbabilityMeasure ℝ}
    (hbound : ∀ m i, ∀ᵐ ω ∂P m, Y m i ω ∈ Icc (0 : ℝ) 1)
    (hlaw : ∀ m i, IdentDistrib (Y m i) id (P m) (ν m : Measure ℝ))
    (hweak : Tendsto ν atTop (𝓝 μ)) {r : ℕ → ℝ} {ρ : ℝ}
    (hr : Tendsto (fun m => r m / N m) atTop (𝓝 ρ))
    (hlower : essInf id (μ : Measure ℝ) < ρ)
    (hmean : ρ < ∫ x, x ∂(μ : Measure ℝ)) :
    (∀ᶠ m in atTop, 0 < (P m).real {ω | rowSum (Y m) ω ≤ r m}) ∧
    Tendsto (fun m => log ((P m).real {ω | rowSum (Y m) ω ≤ r m}) / N m) atTop
      (𝓝 (-lowerRate μ ρ)) := by
  have hν (m : ℕ) : ∀ᵐ x ∂(ν m : Measure ℝ), x ∈ Icc (0 : ℝ) 1 :=
    (hlaw m ⟨0, hNpos m⟩).ae_mem_snd measurableSet_Icc (hbound m ⟨0, hNpos m⟩)
  exact tendsto_log_tail_rows_of_support N hNpos hN P Y hY hind hν
    (unit_support_of_tendsto hν hweak) hlaw hweak hr hlower hmean

end FCAppendix.TriangularCramer

namespace FCAppendix.StrictCramerComparison
open MeasureTheory ProbabilityTheory Filter Topology Set Real
open FCAppendix.ExponentialTilt FCAppendix.BoundedLawConvergence

theorem exponential_ratio_of_log_limit_rows
    (N : ℕ → ℕ) (hNpos : ∀ m, 0 < N m) {a b A : ℕ → ℝ} {L B : ℝ}
    (hpos : ∀ᶠ m in atTop, 0 < b m)
    (hnum : ∀ᶠ m in atTop, a m ≤ exp ((N m : ℝ) * A m))
    (hA : Tendsto A atTop (𝓝 L))
    (hb : Tendsto (fun m => log (b m) / N m) atTop (𝓝 B)) (hgap : L < B) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ m in atTop, a m / b m ≤ exp (-c * N m) := by
  let c := (B - L) / 2
  have hc : 0 < c := by dsimp [c]; linarith
  have ht := (hA.sub hb).eventually_le_const (show L - B < -c by dsimp [c]; linarith)
  refine ⟨c, hc, ?_⟩
  filter_upwards [hpos, hnum, ht] with m hp hn hm
  have hmpos : (0 : ℝ) < N m := Nat.cast_pos.mpr (hNpos m)
  have he : (N m : ℝ) * (A m - log (b m) / N m) = (N m : ℝ) * A m - log (b m) := by
    field_simp
  calc
    a m / b m ≤ exp ((N m : ℝ) * A m) / b m := div_le_div_of_nonneg_right hn hp.le
    _ = exp ((N m : ℝ) * (A m - log (b m) / N m)) := by
      rw [he, exp_sub, exp_log hp]
    _ ≤ exp (-c * N m) := exp_le_exp.mpr (by nlinarith)

theorem tendsto_ratio_zero_of_exponential_bound_rows
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) {a b : ℕ → ℝ}
    (hpos : ∀ᶠ m in atTop, 0 < b m) (ha : ∀ᶠ m in atTop, 0 ≤ a m)
    {c : ℝ} (hc : 0 < c)
    (hbound : ∀ᶠ m in atTop, a m / b m ≤ exp (-c * N m)) :
    Tendsto (fun m => a m / b m) atTop (𝓝 0) := by
  have he : Tendsto (fun m : ℕ => exp (-c * N m)) atTop (𝓝 0) := by
    simpa only [neg_mul, Function.comp_def] using
      tendsto_exp_neg_atTop_nhds_zero.comp ((tendsto_natCast_atTop_atTop.comp hN).const_mul_atTop hc)
  apply squeeze_zero' ?_ hbound he
  filter_upwards [hpos, ha] with m hp ham
  exact div_nonneg ham hp.le

theorem exponential_tail_ratio_rows
    {Ω Ξ : ℕ → Type*} [∀ m, MeasurableSpace (Ω m)] [∀ m, MeasurableSpace (Ξ m)]
    (N : ℕ → ℕ) (hNpos : ∀ m, 0 < N m) (hN : Tendsto N atTop atTop)
    (P : ∀ m, Measure (Ω m)) [∀ m, IsProbabilityMeasure (P m)]
    (Q : ∀ m, Measure (Ξ m)) [∀ m, IsProbabilityMeasure (Q m)]
    (X : ∀ m, Fin (N m) → Ω m → ℝ) (Y : ∀ m, Fin (N m) → Ξ m → ℝ)
    (hX : ∀ m i, Measurable (X m i)) (hY : ∀ m i, Measurable (Y m i))
    (hindX : ∀ m, iIndepFun (X m) (P m)) (hindY : ∀ m, iIndepFun (Y m) (Q m))
    (hXb : ∀ m i, ∀ᵐ ω ∂P m, X m i ω ∈ Icc (0 : ℝ) 1)
    (hYb : ∀ m i, ∀ᵐ ω ∂Q m, Y m i ω ∈ Icc (0 : ℝ) 1)
    {νX νY : ℕ → ProbabilityMeasure ℝ} {μX μY : ProbabilityMeasure ℝ}
    (hlawX : ∀ m i, IdentDistrib (X m i) id (P m) (νX m : Measure ℝ))
    (hlawY : ∀ m i, IdentDistrib (Y m i) id (Q m) (νY m : Measure ℝ))
    (hweakX : Tendsto νX atTop (𝓝 μX)) (hweakY : Tendsto νY atTop (𝓝 μY))
    {r s : ℕ → ℝ} {ρ : ℝ}
    (hr : Tendsto (fun m => r m / N m) atTop (𝓝 ρ))
    (hs : Tendsto (fun m => s m / N m) atTop (𝓝 ρ))
    (hlower : essInf id (μX : Measure ℝ) < ρ)
    (hmean : ρ < ∫ x, x ∂(μX : Measure ℝ))
    (hgap : ∀ u : ℝ, u < 0 → cgf id (μY : Measure ℝ) u < cgf id (μX : Measure ℝ) u) :
    ∃ c : ℝ, 0 < c ∧
      (∀ᶠ m in atTop,
        (Q m).real {ω | rowSum (Y m) ω ≤ s m} /
          (P m).real {ω | rowSum (X m) ω ≤ r m} ≤ exp (-c * N m)) ∧
      Tendsto (fun m => (Q m).real {ω | rowSum (Y m) ω ≤ s m} /
        (P m).real {ω | rowSum (X m) ω ≤ r m}) atTop (𝓝 0) := by
  have hνX (m : ℕ) : ∀ᵐ x ∂(νX m : Measure ℝ), x ∈ Icc (0 : ℝ) 1 :=
    (hlawX m ⟨0, hNpos m⟩).ae_mem_snd measurableSet_Icc (hXb m ⟨0, hNpos m⟩)
  have hνY (m : ℕ) : ∀ᵐ x ∂(νY m : Measure ℝ), x ∈ Icc (0 : ℝ) 1 :=
    (hlawY m ⟨0, hNpos m⟩).ae_mem_snd measurableSet_Icc (hYb m ⟨0, hNpos m⟩)
  have hμX := TriangularCramer.unit_support_of_tendsto hνX hweakX
  have hμY := TriangularCramer.unit_support_of_tendsto hνY hweakY
  obtain ⟨u, hu, hdu⟩ := CramerOptimizer.exists_negative_tilt_of_essInf μX hμX hlower hmean
  have hden := TriangularCramer.tendsto_log_tail_rows N hNpos hN P X hX hindX hXb hlawX hweakX hr hlower hmean
  let A : ℕ → ℝ := fun m => cgf id (νY m : Measure ℝ) u - u * (s m / N m)
  have hcY : Tendsto (fun m => cgf id (νY m : Measure ℝ) u) atTop
      (𝓝 (cgf id (μY : Measure ℝ) u)) :=
    tendsto_cgf hνY hμY hweakY u
  have hA : Tendsto A atTop (𝓝 (cgf id (μY : Measure ℝ) u - u * ρ)) :=
    hcY.sub (hs.const_mul u)
  have hnum : ∀ᶠ m in atTop, (Q m).real {ω | rowSum (Y m) ω ≤ s m} ≤ exp ((N m : ℝ) * A m) := by
    exact Filter.Eventually.of_forall fun m =>
      row_chernoff_bound (Q m) (hY m) (hindY m) (hYb m) (hlawY m) (hNpos m) hu.le
  have hgap' : cgf id (μY : Measure ℝ) u - u * ρ < -CramerOptimizer.lowerRate μX ρ := by
    rw [CramerOptimizer.lowerRate_eq μX hμX hu.le hdu]
    linarith [hgap u hu]
  obtain ⟨c, hc, hbound⟩ := exponential_ratio_of_log_limit_rows N hNpos hden.1 hnum hA hden.2 hgap'
  refine ⟨c, hc, hbound, ?_⟩
  exact tendsto_ratio_zero_of_exponential_bound_rows N hN hden.1
    (Filter.Eventually.of_forall fun m => measureReal_nonneg) hc hbound

end FCAppendix.StrictCramerComparison
