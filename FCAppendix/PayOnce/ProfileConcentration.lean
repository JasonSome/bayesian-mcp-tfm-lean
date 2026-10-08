import FCAppendix.PayOnce.CovarianceConcentration

namespace FCAppendix.PayOnce.CovarianceConcentration
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped BigOperators

theorem mean_gap_le_mean_covariance_ae {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (G : Measure ℝ) [IsProbabilityMeasure G]
    {A B q r : Ω → ℝ} (hA : Measurable A) (hB : Measurable B)
    (hq : Measurable q) (hr : Measurable r)
    (hAb : ∀ ω, A ω ∈ Icc (0 : ℝ) 1) (hBb : ∀ ω, B ω ∈ Icc (0 : ℝ) 1)
    (hqb : ∀ ω, q ω ∈ Icc (0 : ℝ) 1) (hrb : ∀ ω, r ω ∈ Icc (0 : ℝ) 1)
    (horder : ∀ᵐ ω ∂P, 0 ≤ (A ω-B ω)*(q ω-r ω))
    (hlaw : MeasurePreserving (fun ω => (A ω,B ω)) P (G.prod G))
    {η : ℝ} (hη : 0 < η) :
    (∫ ω, |q ω-r ω| ∂P) ≤ (∫ ω, (A ω-B ω)*(q ω-r ω) ∂P)/η +
      (G.prod G).real {z : ℝ × ℝ | |z.1-z.2| < η} := by
  let E := {ω | |A ω-B ω| < η}
  have hE : MeasurableSet E := measurableSet_lt ((hA.sub hB).abs) measurable_const
  have hCi : Integrable (fun ω => (A ω-B ω)*(q ω-r ω)) P := by
    apply Integrable.of_bound ((hA.sub hB).mul (hq.sub hr)).aestronglyMeasurable 1
    apply Eventually.of_forall
    intro ω
    dsimp only [Pi.mul_apply, Pi.sub_apply]
    rw [Real.norm_eq_abs, abs_mul]
    have h1 : |A ω-B ω| ≤ 1 := abs_le.mpr ⟨by linarith [(hAb ω).1, (hBb ω).2],
      by linarith [(hAb ω).2, (hBb ω).1]⟩
    have h2 : |q ω-r ω| ≤ 1 := abs_le.mpr ⟨by linarith [(hqb ω).1, (hrb ω).2],
      by linarith [(hqb ω).2, (hrb ω).1]⟩
    simpa only [one_mul] using mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
  have hIi : Integrable (E.indicator (fun _ => (1 : ℝ))) P := (integrable_const _).indicator hE
  have hh := integral_mono_ae (integrable_abs_gap P hq hr hqb hrb)
    ((hCi.div_const η).add hIi) (horder.mono fun ω hω => by
      simpa only [Pi.add_apply, E, indicator, mem_setOf_eq] using
        pair_gap_le_covariance (hqb ω) (hrb ω) hω hη)
  simp only [Pi.add_apply] at hh
  rw [integral_add (hCi.div_const η) hIi, integral_div,
    integral_indicator hE, setIntegral_const, smul_eq_mul, mul_one] at hh
  have hset : MeasurableSet {z : ℝ × ℝ | |z.1-z.2| < η} :=
    measurableSet_lt ((measurable_fst.sub measurable_snd).abs) measurable_const
  have he : P.real E = (G.prod G).real {z : ℝ × ℝ | |z.1-z.2| < η} := by
    apply congrArg ENNReal.toReal
    exact hlaw.measure_preimage hset.nullMeasurableSet
  simpa only [Pi.add_apply, he] using hh

noncomputable def populationMean {ι : Type*} [Fintype ι] (f : ι → ℝ) : ℝ :=
  (∑ i, f i)/(Fintype.card ι : ℝ)

noncomputable def populationPairMean {ι : Type*} [Fintype ι] (f : ι → ι → ℝ) : ℝ :=
  (∑ i, ∑ j, f i j)/(Fintype.card ι : ℝ)^2

theorem populationPairMean_covariance {ι : Type*} [Fintype ι] (A q : ι → ℝ) :
    populationPairMean (fun i j => (A i-A j)*(q i-q j)) =
      2*(populationMean (fun i => A i*q i)-populationMean A*populationMean q) := by
  unfold populationPairMean populationMean
  rw [pairwise_covariance_sum]
  by_cases hm : (Fintype.card ι : ℝ) = 0
  · simp only [hm, zero_pow (by omega : 2 ≠ 0), div_zero, mul_zero, sub_zero]
  · field_simp

theorem integral_populationPairMean {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) (f : Ω → ι → ι → ℝ) (hf : ∀ i j, Integrable (fun ω => f ω i j) P) :
    (∫ ω, populationPairMean (f ω) ∂P) =
      populationPairMean (fun i j => ∫ ω, f ω i j ∂P) := by
  unfold populationPairMean
  rw [integral_div]
  congr 1
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hf i j))]
  apply Finset.sum_congr rfl
  intro i _
  exact integral_finsetSum _ (fun j _ => hf i j)

theorem populationPairMean_le {ι : Type*} [Fintype ι]
    (hm : 0 < Fintype.card ι) {f g : ι → ι → ℝ} {a b : ℝ}
    (h : ∀ i j, f i j ≤ g i j/a+b) :
    populationPairMean f ≤ populationPairMean g/a+b := by
  have hmR : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hm
  have hh := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) =>
    Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => h i j
  have he : (∑ i, ∑ j, (g i j/a+b)) =
      (∑ i, ∑ j, g i j)/a+(Fintype.card ι : ℝ)^2*b := by
    simp only [Finset.sum_add_distrib, ← Finset.sum_div, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
    ring
  rw [he] at hh
  unfold populationPairMean
  apply (div_le_iff₀ (sq_pos_of_pos hmR)).mpr
  convert hh using 1
  field_simp

theorem integral_pair_gap_le_covariance {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (G : Measure ℝ) [IsProbabilityMeasure G]
    (hm : 0 < Fintype.card ι) (A q : Ω → ι → ℝ)
    (hA : ∀ i, Measurable (fun ω => A ω i)) (hq : ∀ i, Measurable (fun ω => q ω i))
    (hAb : ∀ ω i, A ω i ∈ Icc (0 : ℝ) 1) (hqb : ∀ ω i, q ω i ∈ Icc (0 : ℝ) 1)
    (horder : ∀ᵐ ω ∂P, ∀ i j, 0 ≤ (A ω i-A ω j)*(q ω i-q ω j))
    (hlaw : ∀ i j, i ≠ j → MeasurePreserving (fun ω => (A ω i,A ω j)) P (G.prod G))
    {η : ℝ} (hη : 0 < η) :
    (∫ ω, populationPairMean (fun i j => |q ω i-q ω j|) ∂P) ≤
      2*(∫ ω, populationMean (fun i => A ω i*q ω i)-populationMean (A ω)*populationMean (q ω) ∂P)/η +
        (G.prod G).real {z : ℝ × ℝ | |z.1-z.2| < η} := by
  have hcI (i j : ι) : Integrable (fun ω => (A ω i-A ω j)*(q ω i-q ω j)) P := by
    apply Integrable.of_bound (((hA i).sub (hA j)).mul ((hq i).sub (hq j))).aestronglyMeasurable 1
    apply Eventually.of_forall
    intro ω
    dsimp only [Pi.mul_apply, Pi.sub_apply]
    rw [Real.norm_eq_abs, abs_mul]
    have h1 : |A ω i-A ω j| ≤ 1 := abs_le.mpr ⟨by linarith [(hAb ω i).1, (hAb ω j).2],
      by linarith [(hAb ω i).2, (hAb ω j).1]⟩
    have h2 : |q ω i-q ω j| ≤ 1 := abs_le.mpr ⟨by linarith [(hqb ω i).1, (hqb ω j).2],
      by linarith [(hqb ω i).2, (hqb ω j).1]⟩
    simpa only [one_mul] using mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
  rw [integral_populationPairMean P _ (fun i j => integrable_abs_gap P (hq i) (hq j)
    (fun ω => hqb ω i) (fun ω => hqb ω j))]
  have hh := populationPairMean_le hm (a := η) (b := (G.prod G).real {z : ℝ × ℝ | |z.1-z.2| < η})
    (f := fun i j => ∫ ω, |q ω i-q ω j| ∂P)
    (g := fun i j => ∫ ω, (A ω i-A ω j)*(q ω i-q ω j) ∂P) (fun i j => by
      by_cases he : i = j
      · subst j
        simpa only [sub_self, abs_zero, mul_zero, integral_zero, zero_div, zero_add] using
          measureReal_nonneg (μ := G.prod G) (s := {z : ℝ × ℝ | |z.1-z.2| < η})
      · exact mean_gap_le_mean_covariance_ae P G (hA i) (hA j) (hq i) (hq j)
          (fun ω => hAb ω i) (fun ω => hAb ω j) (fun ω => hqb ω i) (fun ω => hqb ω j)
          (horder.mono fun ω hω => hω i j) (hlaw i j he) hη)
  rw [← integral_populationPairMean P _ hcI] at hh
  simp_rw [populationPairMean_covariance] at hh
  rw [integral_const_mul] at hh
  exact hh

theorem integral_pair_gap_tendsto_zero
    {Ω ι : ℕ → Type*} [∀ t, MeasurableSpace (Ω t)] [∀ t, Fintype (ι t)]
    (P : ∀ t, Measure (Ω t)) [∀ t, IsProbabilityMeasure (P t)]
    (G : Measure ℝ) [IsProbabilityMeasure G] [NullSingletonClass G]
    (hm : ∀ t, 0 < Fintype.card (ι t)) (A q : ∀ t, Ω t → ι t → ℝ)
    (hA : ∀ t i, Measurable (fun ω => A t ω i))
    (hq : ∀ t i, Measurable (fun ω => q t ω i))
    (hAb : ∀ t ω i, A t ω i ∈ Icc (0 : ℝ) 1)
    (hqb : ∀ t ω i, q t ω i ∈ Icc (0 : ℝ) 1)
    (horder : ∀ t, ∀ᵐ ω ∂P t, ∀ i j, 0 ≤ (A t ω i-A t ω j)*(q t ω i-q t ω j))
    (hlaw : ∀ t i j, i ≠ j → MeasurePreserving (fun ω => (A t ω i,A t ω j)) (P t) (G.prod G))
    (hcov : Tendsto (fun t => ∫ ω, populationMean (fun i => A t ω i*q t ω i)-
      populationMean (A t ω)*populationMean (q t ω) ∂P t) atTop (𝓝 0)) :
    Tendsto (fun t => ∫ ω, populationPairMean (fun i j => |q t ω i-q t ω j|) ∂P t)
      atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall fun t => ha.trans_le (integral_nonneg fun ω =>
      div_nonneg (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _) (sq_nonneg _))
  · intro ε hε
    obtain ⟨η,hη,hstrip⟩ := exists_small_diagonal_strip G hε
    have ht : Tendsto (fun t => 2*(∫ ω, populationMean (fun i => A t ω i*q t ω i)-
        populationMean (A t ω)*populationMean (q t ω) ∂P t)/η) atTop (𝓝 0) := by
      simpa only [mul_zero, zero_div] using (hcov.const_mul 2).div_const η
    filter_upwards [ht.eventually_lt_const (sub_pos.mpr hstrip)] with t ht'
    have hh := integral_pair_gap_le_covariance (P t) G (hm t) (A t) (q t) (hA t) (hq t)
      (hAb t) (hqb t) (horder t) (hlaw t) hη
    linarith

theorem integrable_populationPairMean {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) (f : Ω → ι → ι → ℝ) (hf : ∀ i j, Integrable (fun ω => f ω i j) P) :
    Integrable (fun ω => populationPairMean (f ω)) P :=
  (integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hf i j))).div_const _

theorem integral_pair_marginal_gap_tendsto_zero
    {Ω ι : ℕ → Type*} [∀ t, MeasurableSpace (Ω t)] [∀ t, Fintype (ι t)]
    (P : ∀ t, Measure (Ω t)) [∀ t, IsProbabilityMeasure (P t)]
    {n : ℕ} (hn : 0 < n) (hm : ∀ t, 0 < Fintype.card (ι t))
    (p : ∀ t, Ω t → ι t → ℝ)
    (hp : ∀ t i, Measurable (fun ω => p t ω i))
    (hpb : ∀ t ω i, p t ω i ∈ Icc (0 : ℝ) 1)
    (hgap : Tendsto (fun t => ∫ ω, populationPairMean
      (fun i j => |success n (p t ω i)-success n (p t ω j)|) ∂P t) atTop (𝓝 0)) :
    Tendsto (fun t => ∫ ω, populationPairMean (fun i j => |p t ω i-p t ω j|) ∂P t)
      atTop (𝓝 0) := by
  have hpi t := integrable_populationPairMean (P t) (fun ω i j => |p t ω i-p t ω j|)
    (fun i j => integrable_abs_gap (P t) (hp t i) (hp t j) (fun ω => hpb t ω i) (fun ω => hpb t ω j))
  have hsi t := integrable_populationPairMean (P t)
    (fun ω i j => |success n (p t ω i)-success n (p t ω j)|)
    (fun i j => integrable_abs_gap (P t) ((continuous_success n).measurable.comp (hp t i))
      ((continuous_success n).measurable.comp (hp t j))
      (fun ω => success_mem_unit (hpb t ω i)) (fun ω => success_mem_unit (hpb t ω j)))
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall fun t => ha.trans_le (integral_nonneg fun ω =>
      div_nonneg (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _) (sq_nonneg _))
  · intro ε hε
    have ht : Tendsto (fun t => (∫ ω, populationPairMean
        (fun i j => |success n (p t ω i)-success n (p t ω j)|) ∂P t)/(ε/2)^n)
        atTop (𝓝 0) := by simpa only [zero_div] using hgap.div_const ((ε/2)^n)
    filter_upwards [ht.eventually_lt_const (half_pos hε)] with t ht'
    have hh := integral_mono (hpi t) (((hsi t).div_const ((ε/2)^n)).add (integrable_const (ε/2)))
      (fun ω => populationPairMean_le (hm t) (fun i j => by
        have hh := gap_le_success_gap hn (hpb t ω i) (hpb t ω j) (half_pos hε)
        linarith))
    simp only [Pi.add_apply] at hh
    rw [integral_add ((hsi t).div_const _) (integrable_const _), integral_div, integral_const,
      probReal_univ, one_smul] at hh
    linarith

theorem integral_distance_to_capacity_tendsto_zero
    {Ω ι : ℕ → Type*} [∀ t, MeasurableSpace (Ω t)] [∀ t, Fintype (ι t)]
    (P : ∀ t, Measure (Ω t)) [∀ t, IsProbabilityMeasure (P t)]
    (hm : ∀ t, 0 < Fintype.card (ι t)) (p : ∀ t, Ω t → ι t → ℝ)
    (hp : ∀ t i, Measurable (fun ω => p t ω i))
    (hpb : ∀ t ω i, p t ω i ∈ Icc (0 : ℝ) 1)
    (ρt : ℕ → ℝ) {ρ : ℝ} (hρ : Tendsto ρt atTop (𝓝 ρ))
    (hcap : ∀ t, ∀ᵐ ω ∂P t, ∑ i, p t ω i = (Fintype.card (ι t) : ℝ)*ρt t)
    (hgap : Tendsto (fun t => ∫ ω, populationPairMean (fun i j => |p t ω i-p t ω j|) ∂P t)
      atTop (𝓝 0)) :
    Tendsto (fun t => ∫ ω, populationMean (fun i => |p t ω i-ρ|) ∂P t) atTop (𝓝 0) := by
  have hpi t := integrable_populationPairMean (P t) (fun ω i j => |p t ω i-p t ω j|)
    (fun i j => integrable_abs_gap (P t) (hp t i) (hp t j) (fun ω => hpb t ω i) (fun ω => hpb t ω j))
  have hi t : Integrable (fun ω => populationMean (fun i => |p t ω i-ρ|)) (P t) := by
    apply Integrable.div_const
    apply integrable_finsetSum
    intro i _
    exact ((UnitInterval.integrable (P t) _ (hp t i) (fun ω => (hpb t ω i).1)
      (fun ω => (hpb t ω i).2)).sub (integrable_const ρ)).abs
  have hupper : Tendsto (fun t => (∫ ω, populationPairMean (fun i j => |p t ω i-p t ω j|) ∂P t)+|ρt t-ρ|)
      atTop (𝓝 0) := by
    simpa only [sub_self, abs_zero, add_zero] using hgap.add ((hρ.sub_const ρ).abs)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
  · intro t
    exact integral_nonneg fun ω => div_nonneg (Finset.sum_nonneg fun i _ => abs_nonneg _) (Nat.cast_nonneg _)
  · intro t
    have ht := integral_mono_ae (hi t) ((hpi t).add (integrable_const |ρt t-ρ|))
      ((hcap t).mono fun ω hω => by
        have htri : populationMean (fun i => |p t ω i-ρ|) ≤
            populationMean (fun i => |p t ω i-ρt t|)+|ρt t-ρ| := by
          have hmR : (0 : ℝ) < Fintype.card (ι t) := by exact_mod_cast hm t
          have hh := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => abs_sub_le (p t ω i) (ρt t) ρ
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hh
          unfold populationMean
          apply (div_le_iff₀ hmR).mpr
          convert hh using 1
          field_simp
        exact htri.trans (add_le_add (mean_distance_to_capacity_le_pair_gap (hm t) (p t ω) (ρt t) hω) le_rfl))
    simp only [Pi.add_apply] at ht
    rw [integral_add (hpi t) (integrable_const _), integral_const, probReal_univ, one_smul] at ht
    exact ht

end FCAppendix.PayOnce.CovarianceConcentration
