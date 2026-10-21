import FCAppendix.Affine.Uniform06.LiteralRootWindow
import FCAppendix.Affine.Uniform06.RareEmpiricalReplacement

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.RelativeIntegralWindow

open MeasureTheory Set Filter
open scoped Topology

variable {Ω : Type*} [MeasurableSpace Ω]

theorem finite_integral_bound (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P T F H X Y Z : Ω → ℝ) (E : Set Ω) (hE : MeasurableSet E)
    (hP : Measurable P) (hT : Measurable T) (hF : Measurable F) (hH : Measurable H)
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    {N a A B b lo z DX DY DZ : ℝ} (hN : 0< N) (ha : 0≤ a)
    (hA : 0≤ A) (hB : 0≤ B) (hb : 0≤ b) (hlo : 0< lo) (hz : 0< z)
    (q : ℕ)
    (hPb : ∀ᵐ ω ∂μ,P ω ∈ Icc (0:ℝ) 1)
    (hTb : ∀ᵐ ω ∂μ,T ω ∈ Icc (0:ℝ) 1)
    (hFb : ∀ᵐ ω ∂μ,F ω ∈ Icc (0:ℝ) (N^q))
    (hHb : ∀ᵐ ω ∂μ,H ω ∈ Icc (0:ℝ) (N^q))
    (hXb : ∀ᵐ ω ∂μ,X ω ∈ Icc (0:ℝ) DX)
    (hYb : ∀ᵐ ω ∂μ,Y ω ∈ Icc (0:ℝ) DY)
    (hZb : ∀ᵐ ω ∂μ,Z ω ∈ Icc (0:ℝ) DZ)
    (hwin : ∀ᵐ ω ∂μ,ω ∈ E →
      |N^q*P ω-a^q*F ω|≤ A*(1/N+b*(X ω+Y ω/(lo*N)+Z ω/z))*T ω+B*H ω) :
    |N^(q+1)*(∫ ω,P ω ∂μ)-a^q*N*(∫ ω,F ω ∂μ)|≤
      A*((∫ ω,T ω ∂μ)+b*((N*∫ ω,T ω*X ω ∂μ)+
        (∫ ω,T ω*Y ω ∂μ)/lo+(N*∫ ω,T ω*Z ω ∂μ)/z))+
      B*(N*∫ ω,H ω ∂μ)+(1+a^q)*N^(q+1)*μ.real Eᶜ := by
  have hiP := Integrable.of_mem_Icc 0 1 hP.aemeasurable hPb
  have hiT := Integrable.of_mem_Icc 0 1 hT.aemeasurable hTb
  have hiF := Integrable.of_mem_Icc 0 (N^q) hF.aemeasurable hFb
  have hiH := Integrable.of_mem_Icc 0 (N^q) hH.aemeasurable hHb
  have hprod (J : Ω → ℝ) (hJ : Measurable J) (D : ℝ)
      (hJb : ∀ᵐ ω ∂μ,J ω ∈ Icc (0:ℝ) D) : Integrable (fun ω => T ω*J ω) μ := by
    apply Integrable.of_mem_Icc 0 D (hT.mul hJ).aemeasurable
    filter_upwards [hTb,hJb] with ω ht hj
    exact ⟨mul_nonneg ht.1 hj.1,(mul_le_mul_of_nonneg_right ht.2 hj.1).trans
      (by simpa only [one_mul] using hj.2)⟩
  have hiX := hprod X hX DX hXb
  have hiY := hprod Y hY DY hYb
  have hiZ := hprod Z hZ DZ hZb
  let localBound : Ω → ℝ := fun ω => A*((T ω)/N+b*(T ω*X ω+
    (T ω*Y ω)/(lo*N)+(T ω*Z ω)/z))+B*H ω
  have hil : Integrable localBound μ :=
    (((hiT.div_const N).add
      (((hiX.add (hiY.div_const (lo*N))).add (hiZ.div_const z)).const_mul b)).const_mul A).add
      (hiH.const_mul B)
  have hid : Integrable (fun ω => |N^q*P ω-a^q*F ω|) μ :=
    ((hiP.const_mul (N^q)).sub (hiF.const_mul (a^q))).abs
  have hie : Integrable (Eᶜ.indicator (fun _ => (1+a^q)*N^q)) μ :=
    (integrable_const _).indicator hE.compl
  have hpoint : ∀ᵐ ω ∂μ,|N^q*P ω-a^q*F ω|≤
      localBound ω+Eᶜ.indicator (fun _ => (1+a^q)*N^q) ω := by
    filter_upwards [hPb,hTb,hFb,hHb,hXb,hYb,hZb,hwin] with ω hp ht hf hh hx hy hz' hw
    have hloc : 0≤ localBound ω := by
      have ht0 := ht.1
      have hh0 := hh.1
      have hx0 := hx.1
      have hy0 := hy.1
      have hz0 := hz'.1
      dsimp only [localBound]
      positivity
    by_cases he : ω ∈ E
    · rw [indicator_of_notMem (show ω ∉ Eᶜ from by simpa using he),add_zero]
      convert! hw he using 1; dsimp only [localBound]; ring
    · rw [indicator_of_mem (show ω ∈ Eᶜ from he)]
      have hdp := abs_sub (N^q*P ω) (a^q*F ω)
      rw [abs_of_nonneg (mul_nonneg (pow_nonneg hN.le q) hp.1),
        abs_of_nonneg (mul_nonneg (pow_nonneg ha q) hf.1)] at hdp
      have hp' := mul_le_mul_of_nonneg_left hp.2 (pow_nonneg hN.le q)
      have hf' := mul_le_mul_of_nonneg_left hf.2 (pow_nonneg ha q)
      nlinarith
  have hi := integral_mono_ae hid (hil.add hie) hpoint
  simp only [Pi.add_apply] at hi
  rw [integral_add hil hie,integral_indicator hE.compl,setIntegral_const] at hi
  have hlocal : (∫ ω,localBound ω ∂μ)=
      A*((∫ ω,T ω ∂μ)/N+b*((∫ ω,T ω*X ω ∂μ)+
        (∫ ω,T ω*Y ω ∂μ)/(lo*N)+(∫ ω,T ω*Z ω ∂μ)/z))+
        B*(∫ ω,H ω ∂μ) := by
    dsimp only [localBound]
    have hxy : Integrable (fun ω => T ω*X ω+(T ω*Y ω)/(lo*N)) μ :=
      hiX.add (hiY.div_const (lo*N))
    have hxyz : Integrable (fun ω => T ω*X ω+(T ω*Y ω)/(lo*N)+(T ω*Z ω)/z) μ :=
      hxy.add (hiZ.div_const z)
    have hbracket : Integrable (fun ω => T ω/N+b*(T ω*X ω+(T ω*Y ω)/(lo*N)+(T ω*Z ω)/z)) μ :=
      (hiT.div_const N).add (hxyz.const_mul b)
    rw [integral_add (hbracket.const_mul A)
      (hiH.const_mul B),integral_const_mul,
      integral_add (hiT.div_const N) (hxyz.const_mul b),
      integral_div,integral_const_mul,
      integral_add hxy (hiZ.div_const z),
      integral_add hiX (hiY.div_const (lo*N)),integral_div,integral_div,integral_const_mul]
  rw [hlocal] at hi
  have hab : |∫ ω,N^q*P ω-a^q*F ω ∂μ|≤∫ ω,|N^q*P ω-a^q*F ω| ∂μ := by
    simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
      (f:=fun ω => N^q*P ω-a^q*F ω) (μ:=μ)
  rw [integral_sub (hiP.const_mul _) (hiF.const_mul _),integral_const_mul,integral_const_mul] at hab
  have hh := mul_le_mul_of_nonneg_left (hab.trans hi) hN.le
  have hscale : N*|N^q*(∫ ω,P ω ∂μ)-a^q*(∫ ω,F ω ∂μ)|=
      |N*(N^q*(∫ ω,P ω ∂μ)-a^q*(∫ ω,F ω ∂μ))| := by
    rw [abs_mul,abs_of_pos hN]
  rw [hscale] at hh
  convert! hh using 1
  · congr 1
    rw [pow_succ]
    ring
  · simp only [smul_eq_mul,pow_succ]
    field_simp [hN.ne',hlo.ne',hz.ne']

theorem tendsto_zero_of_windows (f : ℕ → ℝ) {B a : ℝ} (_hB : 0≤ B) (ha : 0< a)
    (h : ∀ H≥(0:ℝ),∃ e : ℕ → ℝ,Tendsto e atTop (𝓝 0) ∧
      ∀ᶠ n in atTop,|f n|≤ e n+B*Real.exp (-a*H)) :
    Tendsto f atTop (𝓝 0) := by
  have ht : Tendsto (fun H : ℝ => B*Real.exp (-a*H)) atTop (𝓝 0) := by
    simpa only [mul_zero,Function.comp_def,id_eq] using
      (Real.tendsto_exp_atBot.comp
        ((tendsto_const_mul_atBot_of_neg (neg_lt_zero.mpr ha)).mpr
          (tendsto_id : Tendsto (fun H : ℝ => H) atTop atTop))).const_mul B
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨H,hH0,hH⟩ := ((eventually_ge_atTop (0:ℝ)).and
    (ht.eventually (Iio_mem_nhds (show (0:ℝ)<ε/2 by positivity)))).exists
  obtain ⟨e,he,heb⟩ := h H hH0
  apply eventually_atTop.mp
  filter_upwards [heb,he.eventually (Iio_mem_nhds (show (0:ℝ)<ε/2 by positivity))] with n hn hen
  rw [Real.dist_eq,sub_zero]
  linarith

end FCAppendix.Affine.Uniform06.RelativeIntegralWindow
