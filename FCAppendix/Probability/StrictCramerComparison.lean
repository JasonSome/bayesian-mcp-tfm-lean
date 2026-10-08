import FCAppendix.Probability.TriangularCramer

namespace FCAppendix.StrictCramerComparison
open MeasureTheory ProbabilityTheory Filter Topology Set Real
open FCAppendix.ExponentialTilt FCAppendix.BoundedLawConvergence

theorem cgf_lt_of_order
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X Y : Ω → ℝ} (hX : AEMeasurable X P) (hY : AEMeasurable Y P)
    (hXb : ∀ᵐ ω ∂P, X ω ∈ Icc (0 : ℝ) 1)
    (hYb : ∀ᵐ ω ∂P, Y ω ∈ Icc (0 : ℝ) 1)
    (horder : X ≤ᵐ[P] Y) (hstrict : P {ω | X ω < Y ω} ≠ 0)
    {u : ℝ} (hu : u < 0) : cgf Y P u < cgf X P u := by
  have hiX := integrable_exp_mul_of_bounded P hX hXb u
  have hiY := integrable_exp_mul_of_bounded P hY hYb u
  have hnn : 0 ≤ᵐ[P] (fun ω => exp (u * X ω) - exp (u * Y ω)) :=
    horder.mono fun ω hω => sub_nonneg.mpr (exp_le_exp.mpr (mul_le_mul_of_nonpos_left hω hu.le))
  have hs : {ω | X ω < Y ω} ⊆ Function.support (fun ω => exp (u * X ω) - exp (u * Y ω)) := by
    intro ω hω
    exact (sub_pos.mpr (exp_lt_exp.mpr (mul_lt_mul_of_neg_left hω hu))).ne'
  have hp : 0 < ∫ ω, exp (u * X ω) - exp (u * Y ω) ∂P := by
    apply (integral_pos_iff_support_of_nonneg_ae hnn (hiX.sub hiY)).mpr
    exact pos_iff_ne_zero.mpr (mt (measure_mono_null hs) hstrict)
  rw [integral_sub hiX hiY] at hp
  apply log_lt_log (mgf_pos hiY)
  exact sub_pos.mp hp

theorem exponential_ratio_of_log_limit {a b A : ℕ → ℝ} {L B : ℝ}
    (hpos : ∀ᶠ m in atTop, 0 < b m)
    (hnum : ∀ᶠ m in atTop, a m ≤ exp ((m : ℝ) * A m))
    (hA : Tendsto A atTop (𝓝 L))
    (hb : Tendsto (fun m => log (b m) / m) atTop (𝓝 B)) (hgap : L < B) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ m in atTop, a m / b m ≤ exp (-c * m) := by
  let c := (B - L) / 2
  have hc : 0 < c := by dsimp [c]; linarith
  have ht := (hA.sub hb).eventually_le_const (show L - B < -c by dsimp [c]; linarith)
  refine ⟨c, hc, ?_⟩
  filter_upwards [hpos, hnum, ht, eventually_ge_atTop 1] with m hp hn hm hsize
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hsize
  have he : (m : ℝ) * (A m - log (b m) / m) = (m : ℝ) * A m - log (b m) := by
    field_simp
  calc
    a m / b m ≤ exp ((m : ℝ) * A m) / b m := div_le_div_of_nonneg_right hn hp.le
    _ = exp ((m : ℝ) * (A m - log (b m) / m)) := by
      rw [he, exp_sub, exp_log hp]
    _ ≤ exp (-c * m) := exp_le_exp.mpr (by nlinarith)

theorem tendsto_ratio_zero_of_exponential_bound {a b : ℕ → ℝ}
    (hpos : ∀ᶠ m in atTop, 0 < b m) (ha : ∀ᶠ m in atTop, 0 ≤ a m)
    {c : ℝ} (hc : 0 < c)
    (hbound : ∀ᶠ m in atTop, a m / b m ≤ exp (-c * m)) :
    Tendsto (fun m => a m / b m) atTop (𝓝 0) := by
  have he : Tendsto (fun m : ℕ => exp (-c * m)) atTop (𝓝 0) := by
    simpa only [neg_mul, Function.comp_def] using
      tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_natCast_atTop_atTop.const_mul_atTop hc)
  apply squeeze_zero' ?_ hbound he
  filter_upwards [hpos, ha] with m hp ham
  exact div_nonneg ham hp.le

theorem row_chernoff_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {m : ℕ} {Y : Fin m → Ω → ℝ} (hY : ∀ i, Measurable (Y i))
    (hind : iIndepFun Y P) (hbound : ∀ i, ∀ᵐ ω ∂P, Y i ω ∈ Icc (0 : ℝ) 1)
    {ν : ProbabilityMeasure ℝ} (hlaw : ∀ i, IdentDistrib (Y i) id P (ν : Measure ℝ))
    (hm : 0 < m) {u r : ℝ} (hu : u ≤ 0) :
    P.real {ω | rowSum Y ω ≤ r} ≤ exp ((m : ℝ) * (cgf id (ν : Measure ℝ) u - u * (r / m))) := by
  have ht := integrable_exp_mul_of_bounded P (measurable_rowSum hY).aemeasurable
    (rowSum_bounded P hbound) u
  have hh := measure_le_le_exp_cgf (μ := P) (X := rowSum Y) r hu ht
  let i : Fin m := ⟨0, hm⟩
  rw [cgf_rowSum P hY hbound hind i (fun j => (hlaw j).trans (hlaw i).symm) u,
    cgf_eq_of_identDistrib (hlaw i)] at hh
  convert hh using 2
  have hmne : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  field_simp
  ring

theorem exponential_tail_ratio
    {Ω Ξ : ℕ → Type*} [∀ m, MeasurableSpace (Ω m)] [∀ m, MeasurableSpace (Ξ m)]
    (P : ∀ m, Measure (Ω m)) [∀ m, IsProbabilityMeasure (P m)]
    (Q : ∀ m, Measure (Ξ m)) [∀ m, IsProbabilityMeasure (Q m)]
    (X : ∀ m, Fin m → Ω m → ℝ) (Y : ∀ m, Fin m → Ξ m → ℝ)
    (hX : ∀ m i, Measurable (X m i)) (hY : ∀ m i, Measurable (Y m i))
    (hindX : ∀ m, iIndepFun (X m) (P m)) (hindY : ∀ m, iIndepFun (Y m) (Q m))
    (hXb : ∀ m i, ∀ᵐ ω ∂P m, X m i ω ∈ Icc (0 : ℝ) 1)
    (hYb : ∀ m i, ∀ᵐ ω ∂Q m, Y m i ω ∈ Icc (0 : ℝ) 1)
    {νX νY : ℕ → ProbabilityMeasure ℝ} {μX μY : ProbabilityMeasure ℝ}
    (hlawX : ∀ m i, IdentDistrib (X m i) id (P m) (νX m : Measure ℝ))
    (hlawY : ∀ m i, IdentDistrib (Y m i) id (Q m) (νY m : Measure ℝ))
    (hweakX : Tendsto νX atTop (𝓝 μX)) (hweakY : Tendsto νY atTop (𝓝 μY))
    {r s : ℕ → ℝ} {ρ : ℝ}
    (hr : Tendsto (fun m => r m / m) atTop (𝓝 ρ))
    (hs : Tendsto (fun m => s m / m) atTop (𝓝 ρ))
    (hlower : essInf id (μX : Measure ℝ) < ρ)
    (hmean : ρ < ∫ x, x ∂(μX : Measure ℝ))
    (hgap : ∀ u : ℝ, u < 0 → cgf id (μY : Measure ℝ) u < cgf id (μX : Measure ℝ) u) :
    ∃ c : ℝ, 0 < c ∧
      (∀ᶠ m in atTop,
        (Q m).real {ω | rowSum (Y m) ω ≤ s m} /
          (P m).real {ω | rowSum (X m) ω ≤ r m} ≤ exp (-c * m)) ∧
      Tendsto (fun m => (Q m).real {ω | rowSum (Y m) ω ≤ s m} /
        (P m).real {ω | rowSum (X m) ω ≤ r m}) atTop (𝓝 0) := by
  have hνX (m : ℕ) : ∀ᵐ x ∂(νX (m + 1) : Measure ℝ), x ∈ Icc (0 : ℝ) 1 :=
    (hlawX (m + 1) 0).ae_mem_snd measurableSet_Icc (hXb (m + 1) 0)
  have hνY (m : ℕ) : ∀ᵐ x ∂(νY (m + 1) : Measure ℝ), x ∈ Icc (0 : ℝ) 1 :=
    (hlawY (m + 1) 0).ae_mem_snd measurableSet_Icc (hYb (m + 1) 0)
  have hμX := TriangularCramer.unit_support_of_tendsto hνX (hweakX.comp (tendsto_add_atTop_nat 1))
  have hμY := TriangularCramer.unit_support_of_tendsto hνY (hweakY.comp (tendsto_add_atTop_nat 1))
  obtain ⟨u, hu, hdu⟩ := CramerOptimizer.exists_negative_tilt_of_essInf μX hμX hlower hmean
  have hden := TriangularCramer.tendsto_log_tail P X hX hindX hXb hlawX hweakX hr hlower hmean
  let A : ℕ → ℝ := fun m => cgf id (νY m : Measure ℝ) u - u * (s m / m)
  have hcY : Tendsto (fun m => cgf id (νY m : Measure ℝ) u) atTop
      (𝓝 (cgf id (μY : Measure ℝ) u)) :=
    (tendsto_add_atTop_iff_nat 1).mp
      (tendsto_cgf hνY hμY (hweakY.comp (tendsto_add_atTop_nat 1)) u)
  have hA : Tendsto A atTop (𝓝 (cgf id (μY : Measure ℝ) u - u * ρ)) :=
    hcY.sub (hs.const_mul u)
  have hnum : ∀ᶠ m in atTop, (Q m).real {ω | rowSum (Y m) ω ≤ s m} ≤ exp ((m : ℝ) * A m) := by
    filter_upwards [eventually_ge_atTop 1] with m hm
    exact row_chernoff_bound (Q m) (hY m) (hindY m) (hYb m) (hlawY m) (by omega) hu.le
  have hgap' : cgf id (μY : Measure ℝ) u - u * ρ < -CramerOptimizer.lowerRate μX ρ := by
    rw [CramerOptimizer.lowerRate_eq μX hμX hu.le hdu]
    linarith [hgap u hu]
  obtain ⟨c, hc, hbound⟩ := exponential_ratio_of_log_limit hden.1 hnum hA hden.2 hgap'
  refine ⟨c, hc, hbound, ?_⟩
  exact tendsto_ratio_zero_of_exponential_bound hden.1
    (Filter.Eventually.of_forall fun m => measureReal_nonneg) hc hbound

theorem cgf_gap_of_ordered_laws
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X Y : Ω → ℝ} {μX μY : ProbabilityMeasure ℝ}
    (hlawX : IdentDistrib X id P (μX : Measure ℝ))
    (hlawY : IdentDistrib Y id P (μY : Measure ℝ))
    (hXb : ∀ᵐ ω ∂P, X ω ∈ Icc (0 : ℝ) 1)
    (hYb : ∀ᵐ ω ∂P, Y ω ∈ Icc (0 : ℝ) 1)
    (horder : X ≤ᵐ[P] Y) (hstrict : P {ω | X ω < Y ω} ≠ 0) :
    ∀ u : ℝ, u < 0 → cgf id (μY : Measure ℝ) u < cgf id (μX : Measure ℝ) u := by
  intro u hu
  rw [← cgf_eq_of_identDistrib hlawX, ← cgf_eq_of_identDistrib hlawY]
  exact cgf_lt_of_order P hlawX.aemeasurable_fst hlawY.aemeasurable_fst
    hXb hYb horder hstrict hu

end FCAppendix.StrictCramerComparison
