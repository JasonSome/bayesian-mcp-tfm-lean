import FCAppendix.Affine.Uniform06.SelectedLaplaceLimit
import FCAppendix.Affine.Uniform06.RareEmpiricalReplacement
import FCAppendix.Affine.Uniform06.LiteralCoarseMeasurable

noncomputable section
namespace FCAppendix.Affine.Uniform06.SamplerDenominatorLimit

open MeasureTheory Set Filter
open scoped Topology BigOperators
open FCAppendix.Affine.WeightedSampling
open PathNumerator RareEmpiricalReplacement

lemma inverse_power_lipschitz {c x z : ℝ} (hc : 0 < c)
    (hx : c ≤ x) (hz : c ≤ z) (k : ℕ) :
    |x⁻¹^k-z⁻¹^k| ≤ ((k:ℝ)*(c⁻¹)^(k-1)/c^2)*|x-z| := by
  have hx0 : 0 < x := hc.trans_le hx
  have hz0 : 0 < z := hc.trans_le hz
  have hinv : |x⁻¹-z⁻¹| ≤ |x-z| /c^2 := by
    have hid : x⁻¹-z⁻¹=(z-x)/(x*z) := by
      field_simp [hx0.ne',hz0.ne']
    rw [hid,abs_div,abs_sub_comm,abs_of_pos (mul_pos hx0 hz0)]
    apply div_le_div_of_nonneg_left (abs_nonneg _) (sq_pos_of_pos hc)
    nlinarith [mul_le_mul hx hz hc.le hx0.le]
  have hmax : max |x⁻¹| |z⁻¹| ≤ c⁻¹ := by
    rw [abs_of_pos (inv_pos.mpr hx0),abs_of_pos (inv_pos.mpr hz0)]
    simpa only [one_div] using! max_le (one_div_le_one_div_of_le hc hx) (one_div_le_one_div_of_le hc hz)
  calc
    _ ≤ |x⁻¹-z⁻¹| *(k:ℝ)*(max |x⁻¹| |z⁻¹|)^(k-1) := abs_pow_sub_pow_le _ _ _
    _ ≤ (|x-z| /c^2)*(k:ℝ)*(c⁻¹)^(k-1) :=
      mul_le_mul
        (mul_le_mul_of_nonneg_right hinv (Nat.cast_nonneg k))
        (pow_le_pow_left₀ (le_max_of_le_left (abs_nonneg _)) hmax _)
        (pow_nonneg (le_max_of_le_left (abs_nonneg _)) _) (by positivity)
    _ = _ := by ring

lemma denominator_error {P T x z d c : ℝ} (hT : 0 ≤ T) (hd : 0 ≤ d)
    (hc : 0 < c) (hxc : c ≤ x-d) (hzc : c ≤ z) (k : ℕ)
    (hP : T/x^k ≤ P ∧ P ≤ T/(x-d)^k) :
    |P-T/z^k| ≤ ((k:ℝ)*(c⁻¹)^(k-1)/c^2)*T*(|x-z|+d) := by
  let C := (k:ℝ)*(c⁻¹)^(k-1)/c^2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hxc' : c ≤ x := by linarith
  have h1 := inverse_power_lipschitz hc hxc' hzc k
  have h2 := inverse_power_lipschitz hc hxc hzc k
  have hdabs : |x-d-z| ≤ |x-z|+d := by
    calc
      _ = |(x-z)-d| := by congr 1; ring
      _ ≤ |x-z|+|d| := abs_sub _ _
      _ = _ := by rw [abs_of_nonneg hd]
  have hb1 : |T/x^k-T/z^k| ≤ C*T*(|x-z|+d) := by
    have he : T/x^k-T/z^k=T*(x⁻¹^k-z⁻¹^k) := by simp only [div_eq_mul_inv,inv_pow]; ring
    rw [he,abs_mul,abs_of_nonneg hT]
    calc
      _ ≤ T*(C*|x-z|) := mul_le_mul_of_nonneg_left h1 hT
      _ ≤ T*(C*(|x-z|+d)) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hd) hC) hT
      _ = _ := by ring
  have hb2 : |T/(x-d)^k-T/z^k| ≤ C*T*(|x-z|+d) := by
    have he : T/(x-d)^k-T/z^k=T*((x-d)⁻¹^k-z⁻¹^k) := by
      simp only [div_eq_mul_inv,inv_pow]; ring
    rw [he,abs_mul,abs_of_nonneg hT]
    calc
      _ ≤ T*(C*|x-d-z|) := mul_le_mul_of_nonneg_left h2 hT
      _ ≤ T*(C*(|x-z|+d)) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hdabs hC) hT
      _ = _ := by ring
  rw [abs_le] at hb1 hb2 ⊢
  constructor <;> linarith [hP.1,hP.2]

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem actual_normalized_bracket (w : Weights ι) (k : ℕ) (F : Path ι k → ℝ)
    (hF : ∀ p,0 ≤ F p) {N : ℝ} (hN : 0 < N)
    (hW : (k:ℝ) < totalWeight w) :
    (numeratorSum w k ∅ F/N^k)/(totalWeight w/N)^k ≤ (pathLaw w k ∅).expect F ∧
      (pathLaw w k ∅).expect F ≤
        (numeratorSum w k ∅ F/N^k)/(totalWeight w/N-(k:ℝ)/N)^k := by
  have hh := actual_expectation_bracket w k k ∅ (by simp) hW F hF
  have hW0 : 0 < totalWeight w := (Nat.cast_nonneg k).trans_lt hW
  have hWK : 0 < totalWeight w-(k:ℝ) := sub_pos.mpr hW
  have hleft : (numeratorSum w k ∅ F/N^k)/(totalWeight w/N)^k=
      numeratorSum w k ∅ F/(totalWeight w)^k := by
    rw [div_pow]
    field_simp [hN.ne',hW0.ne']
  have hright : (numeratorSum w k ∅ F/N^k)/(totalWeight w/N-(k:ℝ)/N)^k=
      numeratorSum w k ∅ F/(totalWeight w-(k:ℝ))^k := by
    rw [← sub_div,div_pow]
    field_simp [hN.ne',hWK.ne']
  simpa only [hleft,hright] using hh

theorem actual_denominator_error (w : Weights ι) (k : ℕ) (F : Path ι k → ℝ)
    (hF : ∀ p,0 ≤ F p) {N z c : ℝ} (hN : 0 < N) (hc : 0 < c)
    (hguard : c ≤ totalWeight w/N-(k:ℝ)/N) (hz : c ≤ z) :
    |(pathLaw w k ∅).expect F-(numeratorSum w k ∅ F/N^k)/z^k| ≤
      ((k:ℝ)*(c⁻¹)^(k-1)/c^2)*(numeratorSum w k ∅ F/N^k)*
        (|totalWeight w/N-z|+(k:ℝ)/N) := by
  have hW : (k:ℝ) < totalWeight w := by
    have hh : 0 < (totalWeight w-(k:ℝ))/N := by rw [sub_div]; linarith
    exact sub_pos.mp ((div_pos_iff_of_pos_right hN).mp hh)
  have hT : 0 ≤ numeratorSum w k ∅ F/N^k := by
    apply div_nonneg _ (pow_pos hN k).le
    exact Finset.sum_nonneg (fun p _ => mul_nonneg (numerator_nonneg _ _ _ _) (hF p))
  exact denominator_error hT (div_nonneg (Nat.cast_nonneg k) hN.le) hc hguard hz k
    (actual_normalized_bracket w k F hF hN hW)

section RelativeIntegral

variable {Ω : Type*} [MeasurableSpace Ω]

theorem relative_denominator_replacement
    (μ : ℕ → Measure Ω) [∀ n,IsProbabilityMeasure (μ n)]
    (N : ℕ → ℕ) (hNpos : ∀ n,0 < N n) (hN : Tendsto N atTop atTop)
    (f : ℕ → Ω → ℝ) (hf : ∀ n,Measurable (f n))
    (hfb : ∀ n,∀ᵐ x ∂μ n,f n x ∈ Icc (0:ℝ) 1)
    (P T : (n : ℕ) → (Fin (N n) → Ω) → ℝ)
    (hP : ∀ n,Measurable (P n)) (hT : ∀ n,Measurable (T n))
    (k r : ℕ) {B z L : ℝ} (hB : 0 ≤ B) (hz : 0 < z)
    (hPb : ∀ n,∀ᵐ ω ∂Measure.pi (fun _ : Fin (N n) => μ n),
      0 ≤ P n ω ∧ P n ω ≤ B*(N n:ℝ)^r)
    (hTb : ∀ n,∀ᵐ ω ∂Measure.pi (fun _ : Fin (N n) => μ n),
      0 ≤ T n ω ∧ T n ω ≤ B*(N n:ℝ)^r)
    (hrare : Tendsto (fun n => (N n:ℝ)*∫ ω,T n ω
      ∂Measure.pi (fun _ : Fin (N n) => μ n)) atTop (𝓝 L))
    (hmean : Tendsto (fun n => ∫ x,f n x ∂μ n) atTop (𝓝 z))
    (hpoint : ∀ n,∀ᵐ ω ∂Measure.pi (fun _ : Fin (N n) => μ n),
      z/4 ≤ empirical (f n) (N n) ω-(k:ℝ)/(N n:ℝ) →
      |P n ω-T n ω/z^k| ≤ ((k:ℝ)*((z/4)⁻¹)^(k-1)/(z/4)^2)*T n ω*
        (|empirical (f n) (N n) ω-z|+(k:ℝ)/(N n:ℝ))) :
    Tendsto (fun n => (N n:ℝ)*∫ ω,|P n ω-T n ω/z^k|
      ∂Measure.pi (fun _ : Fin (N n) => μ n)) atTop (𝓝 0) := by
  let Q := fun n => Measure.pi (fun _ : Fin (N n) => μ n)
  let c := z/4
  let C := (k:ℝ)*(c⁻¹)^(k-1)/c^2
  let D := B*(1+z⁻¹^k)
  let bad := fun n => {ω : Fin (N n) → Ω | empirical (f n) (N n) ω < 2*c}
  have hc : 0 < c := by dsimp [c]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hbadmeas (n : ℕ) : MeasurableSet (bad n) :=
    measurableSet_lt (measurable_empirical (hf n) (N n)) measurable_const
  have hNR : Tendsto (fun n => (N n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hN
  have hinv := tendsto_inv_atTop_zero.comp hNR
  have hsmall := (hinv.const_mul (k:ℝ)).eventually
    (Iio_mem_nhds (show (k:ℝ)*0 < c by simpa using hc))
  have hmeanbig := hmean.eventually (Ioi_mem_nhds (show 3*c < z by dsimp [c]; linarith))
  have hTi (n : ℕ) : Integrable (T n) (Q n) :=
    Integrable.of_mem_Icc 0 _ (hT n).aemeasurable (hTb n)
  have hPi (n : ℕ) : Integrable (P n) (Q n) :=
    Integrable.of_mem_Icc 0 _ (hP n).aemeasurable (hPb n)
  have hEi (n : ℕ) : Integrable (fun ω => |P n ω-T n ω/z^k|) (Q n) :=
    ((hPi n).sub ((hTi n).div_const _)).abs
  have hWi (n : ℕ) : Integrable
      (fun ω => T n ω*|empirical (f n) (N n) ω-z|) (Q n) := by
    apply Integrable.of_bound
      ((hT n).mul (((measurable_empirical (hf n) (N n)).sub_const z).abs)).aestronglyMeasurable
      (B*(N n:ℝ)^r*(1+|z|))
    filter_upwards [hTb n,empirical_unit_bounds (μ n) (hfb n) (hNpos n)] with ω ht he
    simp only [Pi.mul_apply]
    rw [Real.norm_of_nonneg (mul_nonneg ht.1 (abs_nonneg _))]
    have hh : |empirical (f n) (N n) ω-z| ≤ 1+|z| := by
      exact (abs_sub _ _).trans (add_le_add
        (by simpa only [abs_of_nonneg he.1] using he.2) le_rfl)
    exact mul_le_mul ht.2 hh (abs_nonneg _) (by positivity)
  have hbadprob : ∀ᶠ n in atTop,(Q n).real (bad n) ≤
      2*Real.exp (-2*(N n:ℝ)*c^2) := by
    filter_upwards [hmeanbig] with n hn
    have hsub : bad n ⊆ {ω | c ≤ |empirical (f n) (N n) ω-∫ x,f n x ∂μ n|} := by
      intro ω hω
      change c ≤ |empirical (f n) (N n) ω-∫ x,f n x ∂μ n|
      have hab := neg_le_abs (empirical (f n) (N n) ω-∫ x,f n x ∂μ n)
      change empirical (f n) (N n) ω < 2*c at hω
      linarith only [hn,hω,hab]
    exact (measureReal_mono hsub).trans
      (FCAppendix.Probability.iid_empiricalMean_two_sided_le (μ n) (hf n).aemeasurable
        (hfb n) (N n) (hNpos n) hc.le)
  have hfinite : ∀ᶠ n in atTop,(N n:ℝ)*∫ ω,|P n ω-T n ω/z^k| ∂Q n ≤
      C*((N n:ℝ)*∫ ω,T n ω*|empirical (f n) (N n) ω-z| ∂Q n)+
      C*((k:ℝ)/(N n:ℝ))*((N n:ℝ)*∫ ω,T n ω ∂Q n)+
      2*D*((N n:ℝ)^(r+1)*Real.exp (-(2*c^2)*(N n:ℝ))) := by
    filter_upwards [hsmall,hbadprob] with n hn hbn
    have hn' : (k:ℝ)/(N n:ℝ) ≤ c := by simpa only [div_eq_mul_inv,Function.comp_def] using! hn.le
    have hNr : 0 < (N n:ℝ) := Nat.cast_pos.mpr (hNpos n)
    have hδ : 0 ≤ (k:ℝ)/(N n:ℝ) := div_nonneg (Nat.cast_nonneg k) hNr.le
    have hbindi : Integrable ((bad n).indicator (fun _ => D*(N n:ℝ)^r)) (Q n) :=
      (integrable_const _).indicator (hbadmeas n)
    have hbound : ∀ᵐ ω ∂Q n,|P n ω-T n ω/z^k| ≤
        C*(T n ω*|empirical (f n) (N n) ω-z|)+
        C*((k:ℝ)/(N n:ℝ))*T n ω+
        (bad n).indicator (fun _ => D*(N n:ℝ)^r) ω := by
      filter_upwards [hPb n,hTb n,hpoint n] with ω hp ht hpt
      by_cases hb : ω ∈ bad n
      · rw [indicator_of_mem hb]
        have h0 : 0 ≤ T n ω/z^k := div_nonneg ht.1 (pow_pos hz k).le
        have hraw : |P n ω-T n ω/z^k| ≤ D*(N n:ℝ)^r := by
          calc
            _ ≤ |P n ω|+|T n ω/z^k| := abs_sub _ _
            _ = P n ω+T n ω/z^k := by rw [abs_of_nonneg hp.1,abs_of_nonneg h0]
            _ ≤ B*(N n:ℝ)^r+(B*(N n:ℝ)^r)/z^k :=
              add_le_add hp.2 (div_le_div_of_nonneg_right ht.2 (pow_pos hz k).le)
            _ = _ := by dsimp [D]; simp only [div_eq_mul_inv,inv_pow]; ring
        linarith [mul_nonneg hC (mul_nonneg ht.1 (abs_nonneg
          (empirical (f n) (N n) ω-z))),mul_nonneg (mul_nonneg hC hδ) ht.1]
      · rw [indicator_of_notMem hb,add_zero]
        have hguard : c ≤ empirical (f n) (N n) ω-(k:ℝ)/(N n:ℝ) := by
          have hem : 2*c ≤ empirical (f n) (N n) ω := le_of_not_gt hb
          linarith
        have hh := hpt hguard
        convert! hh using 1
        dsimp [C,c]
        ring
    have hi := integral_mono_ae (hEi n)
      ((((hWi n).const_mul C).add ((hTi n).const_mul (C*((k:ℝ)/(N n:ℝ))))).add hbindi) hbound
    have hLi : Integrable (fun ω => C*(T n ω*|empirical (f n) (N n) ω-z|)) (Q n) := (hWi n).const_mul C
    have hRi : Integrable (fun ω => C*((k:ℝ)/(N n:ℝ))*T n ω) (Q n) := (hTi n).const_mul _
    have hsum : Integrable (fun ω => C*(T n ω*|empirical (f n) (N n) ω-z|)+
        C*((k:ℝ)/(N n:ℝ))*T n ω) (Q n) := hLi.add hRi
    simp only [Pi.add_apply] at hi
    rw [integral_add hsum hbindi,integral_add hLi hRi,
      integral_const_mul,integral_const_mul,integral_indicator (hbadmeas n),setIntegral_const] at hi
    have hh := mul_le_mul_of_nonneg_left hi hNr.le
    have hbprob := mul_le_mul_of_nonneg_right hbn
      (mul_nonneg hD (pow_nonneg hNr.le r))
    have hbprob' := mul_le_mul_of_nonneg_left hbprob hNr.le
    calc
      _ ≤ (N n:ℝ)*(C*(∫ ω,T n ω*|empirical (f n) (N n) ω-z| ∂Q n)+
          C*((k:ℝ)/(N n:ℝ))*(∫ ω,T n ω ∂Q n)+
          (Q n).real (bad n)*(D*(N n:ℝ)^r)) := hh
      _ ≤ (N n:ℝ)*(C*(∫ ω,T n ω*|empirical (f n) (N n) ω-z| ∂Q n)+
          C*((k:ℝ)/(N n:ℝ))*(∫ ω,T n ω ∂Q n))+
          (N n:ℝ)*((2*Real.exp (-2*(N n:ℝ)*c^2))*(D*(N n:ℝ)^r)) := by
        nlinarith
      _ = _ := by
        rw [show -2*(N n:ℝ)*c^2=-(2*c^2)*(N n:ℝ) by ring,pow_succ]
        ring
  have hmain := rare_empirical_replacement μ f hf hfb N hNpos hN T hT r hB hTb hrare hmean
  have hδzero : Tendsto (fun n => (k:ℝ)/(N n:ℝ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero,Function.comp_def] using! hinv.const_mul (k:ℝ)
  have htail := polynomial_exp_tendsto N hN (r+1) (by positivity : 0 < 2*c^2)
  have hupper := ((hmain.const_mul C).add
    ((hδzero.const_mul C).mul hrare)).add (htail.const_mul (2*D))
  simp only [mul_zero,zero_mul,add_zero] at hupper
  apply squeeze_zero' _ hfinite hupper
  exact Eventually.of_forall fun n => mul_nonneg (Nat.cast_nonneg _)
    (integral_nonneg fun _ => abs_nonneg _)

end RelativeIntegral

end FCAppendix.Affine.Uniform06.SamplerDenominatorLimit
