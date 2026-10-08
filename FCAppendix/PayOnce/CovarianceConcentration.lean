import FCAppendix.PayOnce.JointDerivative
import Mathlib.Probability.IdentDistrib

namespace FCAppendix.PayOnce.CovarianceConcentration
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped BigOperators

theorem exists_small_diagonal_strip (G : Measure ℝ) [IsProbabilityMeasure G]
    [NullSingletonClass G] {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ (G.prod G).real {z : ℝ × ℝ | |z.1-z.2| < δ} < ε := by
  have hne : ∀ᵐ z : ℝ × ℝ ∂G.prod G, z.1 ≠ z.2 := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun measurable_fst measurable_snd).compl).mpr
    exact Filter.Eventually.of_forall fun a => (G.ae_ne a).mono fun _ h => Ne.symm h
  have hzero : G.prod G {z : ℝ × ℝ | z.1 = z.2} = 0 := by
    simpa only [ae_iff, not_not] using hne
  let δ : ℕ → ℝ := fun k => 1 / ((k : ℝ)+1)
  have hδ (k : ℕ) : 0 < δ k := by dsimp only [δ]; positivity
  have hδlim : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let E := fun k => {z : ℝ × ℝ | |z.1-z.2| ≤ δ k}
  have hE (k : ℕ) : MeasurableSet (E k) :=
    measurableSet_le ((measurable_fst.sub measurable_snd).abs) measurable_const
  have hanti : Antitone E := by
    intro i j hij z hz
    change |z.1-z.2| ≤ δ j at hz
    change |z.1-z.2| ≤ δ i
    apply hz.trans
    dsimp only [δ]
    exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hij 1)
  have hinter : (⋂ k, E k) = {z : ℝ × ℝ | z.1 = z.2} := by
    ext z
    simp only [mem_iInter, E, mem_setOf_eq]
    constructor
    · intro hz
      by_contra h
      have hgap : 0 < |z.1-z.2| := abs_pos.mpr (sub_ne_zero.mpr h)
      obtain ⟨k, hk⟩ := (hδlim.eventually_lt_const hgap).exists
      exact hk.not_ge (hz k)
    · intro hz k
      rw [hz, sub_self, abs_zero]
      exact (hδ k).le
  have ht := tendsto_measure_iInter_atTop (fun k => (hE k).nullMeasurableSet) hanti
    (μ := G.prod G) ⟨0, measure_ne_top _ _⟩
  rw [hinter, hzero] at ht
  have htr : Tendsto (fun k => (G.prod G).real (E k)) atTop (𝓝 0) := by
    simpa only [Measure.real, Function.comp_def, ENNReal.toReal_zero] using
      (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp ht
  obtain ⟨k, hk⟩ := (htr.eventually_lt_const hε).exists
  refine ⟨δ k, hδ k, lt_of_le_of_lt ?_ hk⟩
  apply measureReal_mono ?_ (measure_ne_top _ _)
  intro z hz
  change |z.1-z.2| ≤ δ k
  exact hz.le

theorem pair_gap_le_covariance {a b q r η : ℝ}
    (hq : q ∈ Icc (0 : ℝ) 1) (hr : r ∈ Icc (0 : ℝ) 1)
    (horder : 0 ≤ (a-b)*(q-r)) (hη : 0 < η) :
    |q-r| ≤ (a-b)*(q-r)/η + if |a-b| < η then 1 else 0 := by
  have hgap : |q-r| ≤ 1 := abs_le.mpr ⟨by linarith [hq.1, hr.2], by linarith [hq.2, hr.1]⟩
  by_cases hnear : |a-b| < η
  · rw [if_pos hnear]
    linarith [div_nonneg horder hη.le]
  · rw [if_neg hnear, add_zero]
    apply (le_div_iff₀ hη).mpr
    have hh := mul_le_mul_of_nonneg_right (le_of_not_gt hnear) (abs_nonneg (q-r))
    rw [← abs_mul, abs_of_nonneg horder] at hh
    nlinarith

theorem pow_gap_le_success_gap {n : ℕ} (hn : 0 < n) {p q : ℝ}
    (hp : p ∈ Icc (0 : ℝ) 1) (hq : q ∈ Icc (0 : ℝ) 1) :
    |p-q|^n ≤ |success n p-success n q| := by
  wlog hpq : q ≤ p generalizing p q
  · simpa only [abs_sub_comm] using this hq hp (le_of_not_ge hpq)
  have hs : (1-p)^n ≤ (1-q)^n := pow_le_pow_left₀ (sub_nonneg.mpr hp.2) (by linarith) n
  have hh := pow_add_pow_le (sub_nonneg.mpr hpq) (sub_nonneg.mpr hp.2) hn.ne'
  have he : p-q+(1-p) = 1-q := by ring
  rw [he] at hh
  rw [abs_of_nonneg (sub_nonneg.mpr hpq)]
  unfold success
  rw [abs_of_nonneg (by linarith : 0 ≤ 1-(1-p)^n-(1-(1-q)^n))]
  linarith

theorem integrable_abs_gap {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {q r : Ω → ℝ}
    (hq : Measurable q) (hr : Measurable r)
    (hqb : ∀ ω, q ω ∈ Icc (0 : ℝ) 1) (hrb : ∀ ω, r ω ∈ Icc (0 : ℝ) 1) :
    Integrable (fun ω => |q ω-r ω|) P :=
  UnitInterval.integrable P _ (hq.sub hr).abs (fun _ => abs_nonneg _)
    (fun ω => abs_le.mpr ⟨by linarith [(hqb ω).1, (hrb ω).2],
      by linarith [(hqb ω).2, (hrb ω).1]⟩)

theorem mean_gap_le_mean_covariance {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (G : Measure ℝ) [IsProbabilityMeasure G]
    {A B q r : Ω → ℝ} (hA : Measurable A) (hB : Measurable B)
    (hq : Measurable q) (hr : Measurable r)
    (hAb : ∀ ω, A ω ∈ Icc (0 : ℝ) 1) (hBb : ∀ ω, B ω ∈ Icc (0 : ℝ) 1)
    (hqb : ∀ ω, q ω ∈ Icc (0 : ℝ) 1) (hrb : ∀ ω, r ω ∈ Icc (0 : ℝ) 1)
    (horder : ∀ ω, 0 ≤ (A ω-B ω)*(q ω-r ω))
    (hlaw : IdentDistrib (fun ω => (A ω,B ω)) id P (G.prod G))
    {η : ℝ} (hη : 0 < η) :
    (∫ ω, |q ω-r ω| ∂P) ≤ (∫ ω, (A ω-B ω)*(q ω-r ω) ∂P)/η +
      (G.prod G).real {z : ℝ × ℝ | |z.1-z.2| < η} := by
  let E := {ω | |A ω-B ω| < η}
  have hE : MeasurableSet E := measurableSet_lt ((hA.sub hB).abs) measurable_const
  have hCi : Integrable (fun ω => (A ω-B ω)*(q ω-r ω)) P := by
    apply UnitInterval.integrable P _ ((hA.sub hB).mul (hq.sub hr)) horder
    intro ω
    have h1 : |A ω-B ω| ≤ 1 := abs_le.mpr ⟨by linarith [(hAb ω).1, (hBb ω).2],
      by linarith [(hAb ω).2, (hBb ω).1]⟩
    have h2 : |q ω-r ω| ≤ 1 := abs_le.mpr ⟨by linarith [(hqb ω).1, (hrb ω).2],
      by linarith [(hqb ω).2, (hrb ω).1]⟩
    have hh := mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
    rwa [← abs_mul, abs_of_nonneg (horder ω), one_mul] at hh
  have hIi : Integrable (E.indicator (fun _ => (1 : ℝ))) P := (integrable_const _).indicator hE
  have hh := integral_mono (integrable_abs_gap P hq hr hqb hrb)
    ((hCi.div_const η).add hIi) (fun ω => by
      simpa only [Pi.add_apply, E, indicator, mem_setOf_eq] using
        pair_gap_le_covariance (hqb ω) (hrb ω) (horder ω) hη)
  simp only [Pi.add_apply] at hh
  rw [integral_add (hCi.div_const η) hIi, integral_div,
    integral_indicator hE, setIntegral_const, smul_eq_mul, mul_one] at hh
  have he := hlaw.measure_mem_eq (measurableSet_lt
    ((measurable_fst.sub measurable_snd).abs) measurable_const (g := fun _ : ℝ × ℝ => η))
  have he' : P.real E = (G.prod G).real {z : ℝ × ℝ | |z.1-z.2| < η} :=
    congrArg ENNReal.toReal he
  simpa only [Pi.add_apply, he'] using hh

theorem mean_gap_tendsto_zero_of_covariance
    {Ω : ℕ → Type*} [∀ m, MeasurableSpace (Ω m)]
    (P : ∀ m, Measure (Ω m)) [∀ m, IsProbabilityMeasure (P m)]
    (G : Measure ℝ) [IsProbabilityMeasure G] [NullSingletonClass G]
    (A B q r : ∀ m, Ω m → ℝ)
    (hA : ∀ m, Measurable (A m)) (hB : ∀ m, Measurable (B m))
    (hq : ∀ m, Measurable (q m)) (hr : ∀ m, Measurable (r m))
    (hAb : ∀ m ω, A m ω ∈ Icc (0 : ℝ) 1) (hBb : ∀ m ω, B m ω ∈ Icc (0 : ℝ) 1)
    (hqb : ∀ m ω, q m ω ∈ Icc (0 : ℝ) 1) (hrb : ∀ m ω, r m ω ∈ Icc (0 : ℝ) 1)
    (horder : ∀ m ω, 0 ≤ (A m ω-B m ω)*(q m ω-r m ω))
    (hlaw : ∀ m, IdentDistrib (fun ω => (A m ω,B m ω)) id (P m) (G.prod G))
    (hcov : Tendsto (fun m => ∫ ω, (A m ω-B m ω)*(q m ω-r m ω) ∂P m) atTop (𝓝 0)) :
    Tendsto (fun m => ∫ ω, |q m ω-r m ω| ∂P m) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Filter.Eventually.of_forall fun m => ha.trans_le (integral_nonneg fun _ => abs_nonneg _)
  · intro ε hε
    obtain ⟨η, hη, hstrip⟩ := exists_small_diagonal_strip G hε
    have hsmall : ∀ᶠ m in atTop,
        (∫ ω, (A m ω-B m ω)*(q m ω-r m ω) ∂P m)/η <
          ε-(G.prod G).real {z : ℝ × ℝ | |z.1-z.2| < η} := by
      apply Filter.Tendsto.eventually_lt_const (sub_pos.mpr hstrip)
      simpa only [zero_div] using hcov.div_const η
    filter_upwards [hsmall] with m hm
    have hh := mean_gap_le_mean_covariance (P m) G (hA m) (hB m) (hq m) (hr m)
      (hAb m) (hBb m) (hqb m) (hrb m) (horder m) (hlaw m) hη
    linarith

theorem gap_le_success_gap {n : ℕ} (hn : 0 < n) {p q η : ℝ}
    (hp : p ∈ Icc (0 : ℝ) 1) (hq : q ∈ Icc (0 : ℝ) 1) (hη : 0 < η) :
    |p-q| ≤ η + |success n p-success n q|/η^n := by
  by_cases hgap : |p-q| ≤ η
  · exact hgap.trans (le_add_of_nonneg_right (div_nonneg (abs_nonneg _) (pow_nonneg hη.le _)))
  · have hh := (pow_le_pow_left₀ hη.le (le_of_not_ge hgap) n).trans (pow_gap_le_success_gap hn hp hq)
    have hr : 1 ≤ |success n p-success n q|/η^n := (one_le_div (pow_pos hη _)).mpr hh
    have hb : |p-q| ≤ 1 := abs_le.mpr ⟨by linarith [hp.1, hq.2], by linarith [hp.2, hq.1]⟩
    linarith

theorem success_mem_unit {n : ℕ} {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) :
    success n p ∈ Icc (0 : ℝ) 1 := by
  refine ⟨?_, success_le_one n p hp.2⟩
  unfold success
  exact sub_nonneg.mpr (pow_le_one₀ (sub_nonneg.mpr hp.2) (by linarith [hp.1]))

theorem mean_marginal_gap_tendsto_zero
    {Ω : ℕ → Type*} [∀ m, MeasurableSpace (Ω m)]
    (P : ∀ m, Measure (Ω m)) [∀ m, IsProbabilityMeasure (P m)]
    {n : ℕ} (hn : 0 < n) (p q : ∀ m, Ω m → ℝ)
    (hp : ∀ m, Measurable (p m)) (hq : ∀ m, Measurable (q m))
    (hpb : ∀ m ω, p m ω ∈ Icc (0 : ℝ) 1) (hqb : ∀ m ω, q m ω ∈ Icc (0 : ℝ) 1)
    (hgap : Tendsto (fun m => ∫ ω, |success n (p m ω)-success n (q m ω)| ∂P m) atTop (𝓝 0)) :
    Tendsto (fun m => ∫ ω, |p m ω-q m ω| ∂P m) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Filter.Eventually.of_forall fun m => ha.trans_le (integral_nonneg fun _ => abs_nonneg _)
  · intro ε hε
    have hsmall : ∀ᶠ m in atTop,
        (∫ ω, |success n (p m ω)-success n (q m ω)| ∂P m)/(ε/2)^n < ε/2 := by
      apply Filter.Tendsto.eventually_lt_const (half_pos hε)
      simpa only [zero_div] using hgap.div_const ((ε/2)^n)
    filter_upwards [hsmall] with m hm
    have hsI := integrable_abs_gap (P m)
      ((continuous_success n).measurable.comp (hp m)) ((continuous_success n).measurable.comp (hq m))
      (fun ω => success_mem_unit (hpb m ω)) (fun ω => success_mem_unit (hqb m ω))
    have hh := integral_mono (integrable_abs_gap (P m) (hp m) (hq m) (hpb m) (hqb m))
      ((integrable_const (ε/2)).add (hsI.div_const ((ε/2)^n)))
      (fun ω => gap_le_success_gap hn (hpb m ω) (hqb m ω) (half_pos hε))
    simp only [Pi.add_apply] at hh
    rw [integral_add (integrable_const _) (hsI.div_const _), integral_const, probReal_univ,
      one_smul, integral_div] at hh
    simp only [Function.comp_def] at hh
    linarith

theorem mean_distance_to_capacity_le_pair_gap {ι : Type*} [Fintype ι]
    (hm : 0 < Fintype.card ι) (p : ι → ℝ) (ρ : ℝ)
    (hcap : ∑ i, p i = (Fintype.card ι : ℝ)*ρ) :
    (∑ i, |p i-ρ|)/(Fintype.card ι : ℝ) ≤
      (∑ i, ∑ j, |p i-p j|)/(Fintype.card ι : ℝ)^2 := by
  have hmR : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hm
  have hrow (i : ι) : (Fintype.card ι : ℝ)*|p i-ρ| ≤ ∑ j, |p i-p j| := by
    have he : (∑ j, (p i-p j)) = (Fintype.card ι : ℝ)*(p i-ρ) := by
      simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcap]
      ring
    have hh := Finset.abs_sum_le_sum_abs (fun j : ι => p i-p j) Finset.univ
    rw [he, abs_mul, abs_of_pos hmR] at hh
    exact hh
  have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hrow i)
  rw [← Finset.mul_sum] at hh
  apply (div_le_div_iff₀ hmR (sq_pos_of_pos hmR)).mpr
  nlinarith [mul_le_mul_of_nonneg_right hh hmR.le]

theorem pairwise_covariance_sum {ι : Type*} [Fintype ι] (A q : ι → ℝ) :
    (∑ i, ∑ j, (A i-A j)*(q i-q j)) =
      2*(Fintype.card ι : ℝ)*(∑ i, A i*q i) - 2*(∑ i, A i)*(∑ i, q i) := by
  simp_rw [sub_mul, mul_sub, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum, ← Finset.sum_mul]
  ring

theorem empirical_covariance_nonneg {ι : Type*} [Fintype ι]
    (A q : ι → ℝ) (horder : ∀ i j, 0 ≤ (A i-A j)*(q i-q j)) :
    0 ≤ (Fintype.card ι : ℝ)*(∑ i, A i*q i) - (∑ i, A i)*(∑ i, q i) := by
  have hh : 0 ≤ ∑ i, ∑ j, (A i-A j)*(q i-q j) :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => horder i j
  rw [pairwise_covariance_sum] at hh
  linarith

end FCAppendix.PayOnce.CovarianceConcentration
