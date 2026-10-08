import FCAppendix.PayOnce.ProfileConcentration

namespace FCAppendix.PayOnce.CovarianceConcentration
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped BigOperators

theorem weighted_pairwise_covariance_sum {ι : Type*} [Fintype ι] (s A q : ι → ℝ) :
    (∑ i, ∑ j, s i*s j*(A i-A j)*(q i-q j)) =
      2*((∑ i, s i)*(∑ i, s i*A i*q i)-(∑ i, s i*A i)*(∑ i, s i*q i)) := by
  have he (i j : ι) : s i*s j*(A i-A j)*(q i-q j) =
      s j*(s i*A i*q i)-(s i*A i)*(s j*q j)-
        (s i*q i)*(s j*A j)+s i*(s j*A j*q j) := by ring
  simp_rw [he,Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum,← Finset.sum_mul]
  simp_rw [mul_assoc,← Finset.mul_sum]
  ring

theorem populationPairMean_weighted_covariance {ι : Type*} [Fintype ι] (s A q : ι → ℝ) :
    populationPairMean (fun i j => s i*s j*(A i-A j)*(q i-q j)) =
      2*(populationMean s*populationMean (fun i => s i*A i*q i)-
        populationMean (fun i => s i*A i)*populationMean (fun i => s i*q i)) := by
  unfold populationPairMean populationMean
  rw [weighted_pairwise_covariance_sum]
  by_cases hm : (Fintype.card ι : ℝ) = 0
  · simp only [hm,zero_pow (by omega : 2 ≠ 0),div_zero,mul_zero,sub_zero]
  · field_simp

theorem exists_small_positive_diagonal_strip (G : Measure ℝ) [IsProbabilityMeasure G]
    (hatom : ∀ b : ℝ, 0 < b → G {b} = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧
      (G.prod G).real {z : ℝ × ℝ | 0 < z.1 ∧ 0 < z.2 ∧ |z.1-z.2| < δ} < ε := by
  have hzmeas : MeasurableSet {z : ℝ × ℝ | 0 < z.1 ∧ 0 < z.2 ∧ z.1 = z.2} :=
    (measurableSet_lt measurable_const measurable_fst).inter
      ((measurableSet_lt measurable_const measurable_snd).inter
        (measurableSet_eq_fun measurable_fst measurable_snd))
  have hne : ∀ᵐ z : ℝ × ℝ ∂G.prod G, ¬ (0 < z.1 ∧ 0 < z.2 ∧ z.1 = z.2) := by
    apply (Measure.ae_prod_iff_ae_ae hzmeas.compl).mpr
    apply Eventually.of_forall
    intro a
    by_cases ha : 0 < a
    · have hh : ∀ᵐ b ∂G, b ≠ a := by
        rw [ae_iff]
        simp only [not_not]
        change G {a} = 0
        exact hatom a ha
      filter_upwards [hh] with b hb
      exact fun hz => hb hz.2.2.symm
    · exact Eventually.of_forall fun _ hz => ha hz.1
  have hzero : G.prod G {z : ℝ × ℝ | 0 < z.1 ∧ 0 < z.2 ∧ z.1 = z.2} = 0 := by
    simpa only [ae_iff,not_not] using hne
  let δ : ℕ → ℝ := fun j => 1/((j:ℝ)+1)
  have hδ (j : ℕ) : 0 < δ j := by dsimp only [δ]; positivity
  have hδlim : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let E := fun j => {z : ℝ × ℝ | 0 < z.1 ∧ 0 < z.2 ∧ |z.1-z.2| ≤ δ j}
  have hE (j : ℕ) : MeasurableSet (E j) :=
    (measurableSet_lt measurable_const measurable_fst).inter
      ((measurableSet_lt measurable_const measurable_snd).inter
        (measurableSet_le ((measurable_fst.sub measurable_snd).abs) measurable_const))
  have hanti : Antitone E := by
    intro i j hij z hz
    refine ⟨hz.1,hz.2.1,hz.2.2.trans ?_⟩
    dsimp only [δ]
    exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hij 1)
  have hinter : (⋂ j, E j) = {z : ℝ × ℝ | 0 < z.1 ∧ 0 < z.2 ∧ z.1 = z.2} := by
    ext z
    simp only [mem_iInter,E,mem_setOf_eq]
    constructor
    · intro hz
      refine ⟨(hz 0).1,(hz 0).2.1,?_⟩
      by_contra h
      have hgap : 0 < |z.1-z.2| := abs_pos.mpr (sub_ne_zero.mpr h)
      obtain ⟨j,hj⟩ := (hδlim.eventually_lt_const hgap).exists
      exact hj.not_ge (hz j).2.2
    · intro hz j
      refine ⟨hz.1,hz.2.1,?_⟩
      rw [hz.2.2,sub_self,abs_zero]
      exact (hδ j).le
  have ht := tendsto_measure_iInter_atTop (fun j => (hE j).nullMeasurableSet) hanti
    (μ := G.prod G) ⟨0,measure_ne_top _ _⟩
  rw [hinter,hzero] at ht
  have htr : Tendsto (fun j => (G.prod G).real (E j)) atTop (𝓝 0) := by
    simpa only [Measure.real,Function.comp_def,ENNReal.toReal_zero] using
      (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp ht
  obtain ⟨j,hj⟩ := (htr.eventually_lt_const hε).exists
  refine ⟨δ j,hδ j,lt_of_le_of_lt ?_ hj⟩
  apply measureReal_mono ?_ (measure_ne_top _ _)
  intro z hz
  exact ⟨hz.1,hz.2.1,hz.2.2.le⟩

noncomputable def positiveMask (a : ℝ) : ℝ := if 0 < a then 1 else 0

theorem measurable_positiveMask : Measurable positiveMask :=
  measurable_const.ite (measurableSet_lt measurable_const measurable_id) measurable_const

theorem positiveMask_bounds (a : ℝ) : positiveMask a ∈ Icc (0:ℝ) 1 := by
  unfold positiveMask
  split_ifs <;> constructor <;> norm_num

theorem positive_pair_gap_le_covariance {a b q r η : ℝ}
    (hq : q ∈ Icc (0:ℝ) 1) (hr : r ∈ Icc (0:ℝ) 1)
    (horder : 0 < a → 0 < b → 0 ≤ (a-b)*(q-r)) (hη : 0 < η) :
    positiveMask a*positiveMask b*|q-r| ≤
      positiveMask a*positiveMask b*(a-b)*(q-r)/η +
        if 0 < a ∧ 0 < b ∧ |a-b| < η then 1 else 0 := by
  by_cases ha : 0 < a
  · by_cases hb : 0 < b
    · simpa only [positiveMask,ha,hb,if_true,one_mul,true_and] using
        pair_gap_le_covariance hq hr (horder ha hb) hη
    · simp [positiveMask,ha,hb]
  · simp [positiveMask,ha]

theorem norm_positive_pair_mul_le (a b x : ℝ) {C : ℝ} (hx : ‖x‖ ≤ C) :
    ‖positiveMask a*positiveMask b*x‖ ≤ C := by
  have hC := (norm_nonneg x).trans hx
  by_cases ha : 0 < a
  · by_cases hb : 0 < b
    · simpa [positiveMask,ha,hb] using hx
    · simpa [positiveMask,ha,hb] using hC
  · simpa [positiveMask,ha] using hC

theorem mean_positive_gap_le_covariance {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (G : Measure ℝ) [IsProbabilityMeasure G]
    {A B q r : Ω → ℝ} (hA : Measurable A) (hB : Measurable B)
    (hq : Measurable q) (hr : Measurable r)
    (hAb : ∀ ω, A ω ∈ Icc (0:ℝ) 1) (hBb : ∀ ω, B ω ∈ Icc (0:ℝ) 1)
    (hqb : ∀ ω, q ω ∈ Icc (0:ℝ) 1) (hrb : ∀ ω, r ω ∈ Icc (0:ℝ) 1)
    (horder : ∀ᵐ ω ∂P, 0 < A ω → 0 < B ω → 0 ≤ (A ω-B ω)*(q ω-r ω))
    (hlaw : MeasurePreserving (fun ω => (A ω,B ω)) P (G.prod G))
    {η : ℝ} (hη : 0 < η) :
    (∫ ω, positiveMask (A ω)*positiveMask (B ω)*|q ω-r ω| ∂P) ≤
      (∫ ω, positiveMask (A ω)*positiveMask (B ω)*(A ω-B ω)*(q ω-r ω) ∂P)/η +
      (G.prod G).real {z : ℝ × ℝ | 0 < z.1 ∧ 0 < z.2 ∧ |z.1-z.2| < η} := by
  let E := {ω | 0 < A ω ∧ 0 < B ω ∧ |A ω-B ω| < η}
  have hE : MeasurableSet E := (measurableSet_lt measurable_const hA).inter
    ((measurableSet_lt measurable_const hB).inter (measurableSet_lt ((hA.sub hB).abs) measurable_const))
  have hmask := (measurable_positiveMask.comp hA).mul (measurable_positiveMask.comp hB)
  have hgapb (ω) : |q ω-r ω| ≤ 1 := abs_le.mpr
    ⟨by linarith [(hqb ω).1,(hrb ω).2],by linarith [(hqb ω).2,(hrb ω).1]⟩
  have hGi : Integrable (fun ω => positiveMask (A ω)*positiveMask (B ω)*|q ω-r ω|) P :=
    Integrable.of_bound (hmask.mul (hq.sub hr).abs).aestronglyMeasurable 1
      (Eventually.of_forall fun ω => norm_positive_pair_mul_le _ _ _ (by
        simpa only [Real.norm_eq_abs,abs_abs] using hgapb ω))
  have hCi : Integrable (fun ω => positiveMask (A ω)*positiveMask (B ω)*(A ω-B ω)*(q ω-r ω)) P := by
    apply Integrable.of_bound ((hmask.mul (hA.sub hB)).mul (hq.sub hr)).aestronglyMeasurable 1
    apply Eventually.of_forall
    intro ω
    dsimp only [Pi.mul_apply,Pi.sub_apply,Function.comp_apply]
    rw [mul_assoc (positiveMask (A ω)*positiveMask (B ω))]
    apply norm_positive_pair_mul_le
    rw [Real.norm_eq_abs,abs_mul]
    have htype : |A ω-B ω| ≤ 1 := abs_le.mpr
      ⟨by linarith [(hAb ω).1,(hBb ω).2],by linarith [(hAb ω).2,(hBb ω).1]⟩
    simpa only [one_mul] using mul_le_mul htype (hgapb ω) (abs_nonneg _) zero_le_one
  have hIi : Integrable (E.indicator (fun _ => (1:ℝ))) P := (integrable_const _).indicator hE
  have hh := integral_mono_ae hGi ((hCi.div_const η).add hIi) (horder.mono fun ω hω => by
    simpa only [Pi.add_apply,E,indicator,mem_setOf_eq] using
      positive_pair_gap_le_covariance (hqb ω) (hrb ω) hω hη)
  simp only [Pi.add_apply] at hh
  rw [integral_add (hCi.div_const η) hIi,integral_div,integral_indicator hE,
    setIntegral_const,smul_eq_mul,mul_one] at hh
  have hset : MeasurableSet {z : ℝ × ℝ | 0 < z.1 ∧ 0 < z.2 ∧ |z.1-z.2| < η} :=
    (measurableSet_lt measurable_const measurable_fst).inter
      ((measurableSet_lt measurable_const measurable_snd).inter
        (measurableSet_lt ((measurable_fst.sub measurable_snd).abs) measurable_const))
  have he : P.real E = (G.prod G).real {z : ℝ × ℝ | 0 < z.1 ∧ 0 < z.2 ∧ |z.1-z.2| < η} := by
    apply congrArg ENNReal.toReal
    exact hlaw.measure_preimage hset.nullMeasurableSet
  simpa only [he] using hh

theorem integrable_positive_pair_gap {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {A B q r : Ω → ℝ}
    (hA : Measurable A) (hB : Measurable B) (hq : Measurable q) (hr : Measurable r)
    (hqb : ∀ ω, q ω ∈ Icc (0:ℝ) 1) (hrb : ∀ ω, r ω ∈ Icc (0:ℝ) 1) :
    Integrable (fun ω => positiveMask (A ω)*positiveMask (B ω)*|q ω-r ω|) P := by
  apply Integrable.of_bound
    (((measurable_positiveMask.comp hA).mul (measurable_positiveMask.comp hB)).mul
      (hq.sub hr).abs).aestronglyMeasurable 1
  apply Eventually.of_forall
  intro ω
  dsimp only [Pi.mul_apply,Pi.sub_apply,Function.comp_apply]
  apply norm_positive_pair_mul_le
  rw [Real.norm_eq_abs,abs_abs]
  exact abs_le.mpr ⟨by linarith [(hqb ω).1,(hrb ω).2],by linarith [(hqb ω).2,(hrb ω).1]⟩

theorem integral_positive_pair_gap_le_covariance
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (G : Measure ℝ) [IsProbabilityMeasure G]
    (hm : 0 < Fintype.card ι) (A q : Ω → ι → ℝ)
    (hA : ∀ i, Measurable (fun ω => A ω i)) (hq : ∀ i, Measurable (fun ω => q ω i))
    (hAb : ∀ ω i, A ω i ∈ Icc (0:ℝ) 1) (hqb : ∀ ω i, q ω i ∈ Icc (0:ℝ) 1)
    (horder : ∀ᵐ ω ∂P, ∀ i j, 0 < A ω i → 0 < A ω j →
      0 ≤ (A ω i-A ω j)*(q ω i-q ω j))
    (hlaw : ∀ i j, i ≠ j → MeasurePreserving (fun ω => (A ω i,A ω j)) P (G.prod G))
    {η : ℝ} (hη : 0 < η) :
    let s := fun ω i => positiveMask (A ω i)
    (∫ ω, populationPairMean (fun i j => s ω i*s ω j*|q ω i-q ω j|) ∂P) ≤
      2*(∫ ω, populationMean (s ω)*populationMean (fun i => s ω i*A ω i*q ω i)-
        populationMean (fun i => s ω i*A ω i)*populationMean (fun i => s ω i*q ω i) ∂P)/η +
      (G.prod G).real {z : ℝ × ℝ | 0 < z.1 ∧ 0 < z.2 ∧ |z.1-z.2| < η} := by
  dsimp only
  have hcI (i j : ι) : Integrable (fun ω => positiveMask (A ω i)*positiveMask (A ω j)*
      (A ω i-A ω j)*(q ω i-q ω j)) P := by
    apply Integrable.of_bound
      ((((measurable_positiveMask.comp (hA i)).mul (measurable_positiveMask.comp (hA j))).mul
        ((hA i).sub (hA j))).mul ((hq i).sub (hq j))).aestronglyMeasurable 1
    apply Eventually.of_forall
    intro ω
    dsimp only [Pi.mul_apply,Pi.sub_apply,Function.comp_apply]
    rw [mul_assoc (positiveMask (A ω i)*positiveMask (A ω j))]
    apply norm_positive_pair_mul_le
    rw [Real.norm_eq_abs,abs_mul]
    have h1 : |A ω i-A ω j| ≤ 1 := abs_le.mpr
      ⟨by linarith [(hAb ω i).1,(hAb ω j).2],by linarith [(hAb ω i).2,(hAb ω j).1]⟩
    have h2 : |q ω i-q ω j| ≤ 1 := abs_le.mpr
      ⟨by linarith [(hqb ω i).1,(hqb ω j).2],by linarith [(hqb ω i).2,(hqb ω j).1]⟩
    simpa only [one_mul] using mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
  rw [integral_populationPairMean P _ (fun i j => integrable_positive_pair_gap P
    (hA i) (hA j) (hq i) (hq j) (fun ω => hqb ω i) (fun ω => hqb ω j))]
  have hh := populationPairMean_le hm
    (a := η) (b := (G.prod G).real {z : ℝ × ℝ | 0 < z.1 ∧ 0 < z.2 ∧ |z.1-z.2| < η})
    (f := fun i j => ∫ ω, positiveMask (A ω i)*positiveMask (A ω j)*|q ω i-q ω j| ∂P)
    (g := fun i j => ∫ ω, positiveMask (A ω i)*positiveMask (A ω j)*(A ω i-A ω j)*(q ω i-q ω j) ∂P)
    (fun i j => by
      by_cases he : i = j
      · subst j
        simpa only [sub_self,abs_zero,mul_zero,integral_zero,zero_div,zero_add] using
          measureReal_nonneg (μ := G.prod G) (s := {z : ℝ × ℝ | 0 < z.1 ∧ 0 < z.2 ∧ |z.1-z.2| < η})
      · exact mean_positive_gap_le_covariance P G (hA i) (hA j) (hq i) (hq j)
          (fun ω => hAb ω i) (fun ω => hAb ω j) (fun ω => hqb ω i) (fun ω => hqb ω j)
          (horder.mono fun ω hω => hω i j) (hlaw i j he) hη)
  rw [← integral_populationPairMean P _ hcI] at hh
  simp_rw [populationPairMean_weighted_covariance] at hh
  rw [integral_const_mul] at hh
  exact hh

theorem integral_positive_pair_gap_tendsto_zero
    {Ω ι : ℕ → Type*} [∀ t, MeasurableSpace (Ω t)] [∀ t, Fintype (ι t)]
    (P : ∀ t, Measure (Ω t)) [∀ t, IsProbabilityMeasure (P t)]
    (G : Measure ℝ) [IsProbabilityMeasure G]
    (hatom : ∀ b : ℝ, 0 < b → G {b} = 0)
    (hm : ∀ t, 0 < Fintype.card (ι t)) (A q : ∀ t, Ω t → ι t → ℝ)
    (hA : ∀ t i, Measurable (fun ω => A t ω i))
    (hq : ∀ t i, Measurable (fun ω => q t ω i))
    (hAb : ∀ t ω i, A t ω i ∈ Icc (0:ℝ) 1)
    (hqb : ∀ t ω i, q t ω i ∈ Icc (0:ℝ) 1)
    (horder : ∀ t, ∀ᵐ ω ∂P t, ∀ i j, 0 < A t ω i → 0 < A t ω j →
      0 ≤ (A t ω i-A t ω j)*(q t ω i-q t ω j))
    (hlaw : ∀ t i j, i ≠ j → MeasurePreserving
      (fun ω => (A t ω i,A t ω j)) (P t) (G.prod G))
    (hcov : Tendsto (fun t => ∫ ω,
      populationMean (fun i => positiveMask (A t ω i))*populationMean (fun i => positiveMask (A t ω i)*A t ω i*q t ω i)-
      populationMean (fun i => positiveMask (A t ω i)*A t ω i)*populationMean (fun i => positiveMask (A t ω i)*q t ω i)
      ∂P t) atTop (𝓝 0)) :
    Tendsto (fun t => ∫ ω, populationPairMean (fun i j =>
      positiveMask (A t ω i)*positiveMask (A t ω j)*|q t ω i-q t ω j|) ∂P t)
      atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall fun t => ha.trans_le (integral_nonneg fun ω =>
      div_nonneg (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
        mul_nonneg (mul_nonneg (positiveMask_bounds _).1 (positiveMask_bounds _).1) (abs_nonneg _)) (sq_nonneg _))
  · intro ε hε
    obtain ⟨η,hη,hstrip⟩ := exists_small_positive_diagonal_strip G hatom hε
    have ht := (hcov.const_mul 2).div_const η
    simp only [mul_zero,zero_div] at ht
    filter_upwards [ht.eventually_lt_const (sub_pos.mpr hstrip)] with t ht'
    have hh := integral_positive_pair_gap_le_covariance (P t) G (hm t) (A t) (q t)
      (hA t) (hq t) (hAb t) (hqb t) (horder t) (hlaw t) hη
    dsimp only at hh
    linarith

end FCAppendix.PayOnce.CovarianceConcentration
