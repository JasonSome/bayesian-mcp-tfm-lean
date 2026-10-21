import FCAppendix.Affine.Uniform06.MovingKernelLimits
import FCAppendix.Affine.Uniform06.RareEmpiricalReplacement

noncomputable section
namespace FCAppendix.Affine.Uniform06.DerivativeScaleLimits

open Filter Set
open scoped Topology
open MovingKernelLimits RareEmpiricalReplacement

theorem lower_power_vanish (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (hNp : ∀ n,0< N n) (f : ℕ → ℝ) (k : ℕ) {B : ℝ} (hB : 0≤ B)
    (hf : ∀ᶠ n in atTop,|(N n:ℝ)^(k+1)*f n|≤ B) :
    Tendsto (fun n => (N n:ℝ)^k*f n) atTop (𝓝 0) := by
  have hn : Tendsto (fun n => (N n:ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hN
  have hi : Tendsto (fun n => (N n:ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hn
  have hh := bounded_mul_zero hB hf hi
  apply hh.congr
  intro n
  have hn0 : (N n:ℝ)≠0 := ne_of_gt (by exact_mod_cast hNp n)
  rw [pow_succ]
  field_simp [hn0]

theorem main_errors (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (hNp : ∀ n,0< N n) (b C R Z E1 E2 : ℕ → ℝ)
    {b0 lo ξ γ a B : ℝ} (hblim : Tendsto b atTop (𝓝 b0))
    (hlo : 0< lo) (hlb0 : lo< b0) (hξ : 0<ξ) (hγ : 0<γ)
    (ha : 0< a) (hB : 0≤ B)
    (hC : ∀ᶠ n in atTop,|(N n:ℝ)^2*C n|≤ B)
    (hR : ∀ᶠ n in atTop,|(N n:ℝ)^3*R n|≤ B)
    (hZ : ∀ᶠ n in atTop,|(N n:ℝ)*Z n|≤ B)
    (hE : ∀ᶠ n in atTop,
      0≤ E1 n ∧ 0≤ E2 n ∧
      E1 n≤ C n/(b n-lo)+Z n/(ξ*(b n)^2*γ*(N n:ℝ))+
        16/(ξ*b n)*Real.exp (-a*(N n:ℝ)) ∧
      E2 n≤2*R n/(b n-lo)+2*C n/(ξ*(b n)^2*γ*(N n:ℝ))+
        32/(ξ*b n)*Real.exp (-a*(N n:ℝ))) :
    Tendsto (fun n => (N n:ℝ)*E1 n) atTop (𝓝 0) ∧
    Tendsto (fun n => (N n:ℝ)^2*E2 n) atTop (𝓝 0) := by
  have hb0 : 0< b0 := hlo.trans hlb0
  have hNC := lower_power_vanish N hN hNp C 1 hB (by simpa only [Nat.reduceAdd] using hC)
  have hNNR := lower_power_vanish N hN hNp R 2 hB (by simpa only [Nat.reduceAdd] using hR)
  have hZ0 := lower_power_vanish N hN hNp Z 0 hB (by simpa only [Nat.reduceAdd,pow_one] using hZ)
  simp only [pow_one] at hNC
  simp only [pow_zero,one_mul] at hZ0
  have hden : ξ*b0^2*γ≠0 := ne_of_gt (by positivity)
  have hdenlim := ((hblim.pow 2).const_mul ξ).mul_const γ
  have hgplim := hblim.sub_const lo
  have hxlim := hblim.const_mul ξ
  have hg0 : b0-lo≠0 := (sub_pos.mpr hlb0).ne'
  have hx0 : ξ*b0≠0 := (mul_pos hξ hb0).ne'
  have h1 := ((hNC.div hgplim hg0).add (hZ0.div hdenlim hden)).add
    ((((tendsto_const_nhds : Tendsto (fun _ : ℕ => (16:ℝ)) atTop (𝓝 16)).div hxlim hx0).mul
      (polynomial_exp_tendsto N hN 1 ha)))
  have h2 := (((hNNR.const_mul 2).div hgplim hg0).add
      ((hNC.const_mul 2).div hdenlim hden)).add
    ((((tendsto_const_nhds : Tendsto (fun _ : ℕ => (32:ℝ)) atTop (𝓝 32)).div hxlim hx0).mul
      (polynomial_exp_tendsto N hN 2 ha)))
  have h1' : Tendsto (fun n => (N n:ℝ)*C n/(b n-lo)+
      Z n/(ξ*(b n)^2*γ)+16/(ξ*b n)*((N n:ℝ)*Real.exp (-a*(N n:ℝ))))
      atTop (𝓝 0) := by
    simpa only [Pi.div_apply,pow_one,zero_div,zero_add,mul_zero] using h1
  have h2' : Tendsto (fun n => 2*((N n:ℝ)^2*R n)/(b n-lo)+
      2*((N n:ℝ)*C n)/(ξ*(b n)^2*γ)+
      32/(ξ*b n)*((N n:ℝ)^2*Real.exp (-a*(N n:ℝ)))) atTop (𝓝 0) := by
    simpa only [Pi.div_apply,zero_mul,zero_div,zero_add,mul_zero] using h2
  have hbb := hblim.eventually (Ioi_mem_nhds hlb0)
  constructor
  · apply squeeze_zero' _ _ h1'
    · filter_upwards [hE] with n hn
      exact mul_nonneg (Nat.cast_nonneg _) hn.1
    · filter_upwards [hE,hbb] with n hn hb
      have hn0 : (N n:ℝ)≠0 := ne_of_gt (by exact_mod_cast hNp n)
      have hh := mul_le_mul_of_nonneg_left hn.2.2.1 (Nat.cast_nonneg (N n))
      have hbp : 0< b n := hlo.trans hb
      convert! hh using 1
      field_simp [hn0,hξ.ne',hγ.ne',hbp.ne',(sub_pos.mpr hb).ne']
  · apply squeeze_zero' _ _ h2'
    · filter_upwards [hE] with n hn
      exact mul_nonneg (sq_nonneg _) hn.2.1
    · filter_upwards [hE,hbb] with n hn hb
      have hn0 : (N n:ℝ)≠0 := ne_of_gt (by exact_mod_cast hNp n)
      have hh := mul_le_mul_of_nonneg_left hn.2.2.2 (sq_nonneg (N n:ℝ))
      have hbp : 0< b n := hlo.trans hb
      convert! hh using 1
      field_simp [hn0,hξ.ne',hγ.ne',hbp.ne',(sub_pos.mpr hb).ne']

theorem guard_error (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (hNp : ∀ n,0< N n) (F U K J : ℕ → ℝ) (q : ℕ)
    {K0 J0 B a : ℝ} (hK0 : 0≤ K0) (hJ0 : 0≤ J0) (_hB : 0≤ B) (ha : 0< a)
    (hU : ∀ᶠ n in atTop,0≤ U n ∧ (N n:ℝ)*U n≤ B)
    (hK : ∀ᶠ n in atTop,0≤ K n ∧ K n≤ K0/(N n:ℝ))
    (hJ : ∀ᶠ n in atTop,0≤ J n ∧ J n≤ J0)
    (hF : ∀ᶠ n in atTop,0≤ F n ∧
      F n≤ K n*(J n/(N n:ℝ))^q*U n+
        8*K n*Real.exp (-a*(N n:ℝ))) :
    Tendsto (fun n => (N n:ℝ)^q*F n) atTop (𝓝 0) := by
  have hn : Tendsto (fun n => (N n:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hN
  have hi : Tendsto (fun n => (N n:ℝ)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hn
  have hhead : Tendsto (fun n => K0*J0^q*B/(N n:ℝ)^2) atTop (𝓝 0) := by
    simpa only [zero_pow (by norm_num : (2:ℕ)≠0),mul_zero,div_eq_mul_inv,
      inv_pow] using (hi.pow 2).const_mul (K0*J0^q*B)
  have htail : Tendsto (fun n => 8*K0*((N n:ℝ)^q*Real.exp (-a*(N n:ℝ))))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using (polynomial_exp_tendsto N hN q ha).const_mul (8*K0)
  have ht : Tendsto (fun n => K0*J0^q*B/(N n:ℝ)^2+
      8*K0*((N n:ℝ)^q*Real.exp (-a*(N n:ℝ)))) atTop (𝓝 0) := by
    simpa only [zero_add] using hhead.add htail
  apply squeeze_zero' _ _ ht
  · filter_upwards [hF] with n hn
    exact mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) hn.1
  · filter_upwards [hF,hU,hK,hJ] with n hf hu hk hj
    have hnp : (0:ℝ)< N n := by exact_mod_cast hNp n
    have hn1 : (1:ℝ)≤ N n := by exact_mod_cast hNp n
    have huB : U n≤ B/(N n:ℝ) := (le_div_iff₀ hnp).mpr (by nlinarith [hu.2])
    have hkB : K n≤ K0 := hk.2.trans ((div_le_iff₀ hnp).mpr (by nlinarith))
    have hp : (J n/(N n:ℝ))^q≤(J0/(N n:ℝ))^q :=
      pow_le_pow_left₀ (div_nonneg hj.1 hnp.le) (div_le_div_of_nonneg_right hj.2 hnp.le) q
    have hmain := mul_le_mul (mul_le_mul hk.2 hp
      (pow_nonneg (div_nonneg hj.1 hnp.le) q) (div_nonneg hK0 hnp.le)) huB
      hu.1 (mul_nonneg (div_nonneg hK0 hnp.le) (pow_nonneg (div_nonneg hJ0 hnp.le) q))
    have htail' := mul_le_mul_of_nonneg_right hkB (Real.exp_pos (-a*(N n:ℝ))).le
    have hh := mul_le_mul_of_nonneg_left hf.2 (pow_nonneg hnp.le q)
    have hmain' := mul_le_mul_of_nonneg_left hmain (pow_nonneg hnp.le q)
    have hmainEq : (N n:ℝ)^q*((K0/(N n:ℝ))*(J0/(N n:ℝ))^q*(B/(N n:ℝ)))=
        K0*J0^q*B/(N n:ℝ)^2 := by
      rw [div_pow]
      field_simp [hnp.ne']
    rw [hmainEq] at hmain'
    nlinarith [mul_le_mul_of_nonneg_left htail' (show 0≤8*(N n:ℝ)^q by positivity)]

end FCAppendix.Affine.Uniform06.DerivativeScaleLimits
