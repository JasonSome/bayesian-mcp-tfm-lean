import FCAppendix.Affine.Uniform06.EntryLaplace

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.EntryWeightedLaplace
open MeasureTheory ProbabilityTheory Set Filter Topology
open FCAppendix.ExponentialTilt
open FCAppendix.Affine.Uniform06.EntryLaplace
universe u
local notation "φ0" => gaussianPDFReal 0 1 0

section Finite
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]

lemma measurable_strictLaplace (θ : ℝ) {W : Ω → ℝ} (hW : Measurable W) :
    Measurable (fun ω => strictLaplace θ (W ω)) := by
  unfold strictLaplace
  exact Measurable.ite (measurableSet_lt measurable_const hW)
    (Real.measurable_exp.comp (measurable_const.mul hW)) measurable_const

lemma measurable_finiteDifference (θ h : ℝ) (k : ℕ) {W : Ω → ℝ}
    (hW : Measurable W) : Measurable (fun ω => finiteDifference θ h k (W ω)) := by
  unfold finiteDifference
  apply Measurable.ite (measurableSet_lt measurable_const hW) ?_ measurable_const
  fun_prop

lemma measurable_weightedMonomial (θ : ℝ) (k : ℕ) {W : Ω → ℝ}
    (hW : Measurable W) : Measurable (fun ω => weightedMonomial θ k (W ω)) := by
  unfold weightedMonomial
  apply Measurable.ite (measurableSet_lt measurable_const hW) ?_ measurable_const
  fun_prop

lemma strictLaplace_bounds {θ : ℝ} (hθ : 0 ≤ θ) (W : ℝ) :
    strictLaplace θ W ∈ Icc (0 : ℝ) 1 := by
  by_cases hW : 0 < W
  · simp only [strictLaplace,if_pos hW,mem_Icc]
    exact ⟨(Real.exp_pos _).le,Real.exp_le_one_iff.mpr (by nlinarith)⟩
  · simp [strictLaplace,hW]

lemma integrable_strictLaplace {W : Ω → ℝ} (hW : Measurable W)
    {θ : ℝ} (hθ : 0 ≤ θ) : Integrable (fun ω => strictLaplace θ (W ω)) μ := by
  apply Integrable.of_bound (measurable_strictLaplace θ hW).aestronglyMeasurable 1
  exact Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs,abs_of_nonneg (strictLaplace_bounds hθ _).1]
    exact (strictLaplace_bounds hθ _).2

lemma finiteDifference_bounds {θ h : ℝ} (hθ : 0 ≤ θ) (hh : 0 < h)
    (k : ℕ) (W : ℝ) : finiteDifference θ h k W ∈ Icc (0 : ℝ) (1/h^k) := by
  by_cases hW : 0 < W
  · simp only [finiteDifference,if_pos hW,mem_Icc]
    have he : Real.exp (-h*W) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    have hp : 0 ≤ (1-Real.exp (-h*W))^k := pow_nonneg (by linarith) _
    have hpow : (1-Real.exp (-h*W))^k ≤ 1 := by
      simpa using pow_le_pow_left₀ (by linarith : 0 ≤ 1-Real.exp (-h*W))
        (show 1-Real.exp (-h*W) ≤ 1 by linarith [Real.exp_pos (-h*W)]) k
    have hE : Real.exp (-θ*W) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    exact ⟨by positivity,div_le_div_of_nonneg_right
      (by nlinarith [Real.exp_pos (-θ*W)]) (pow_nonneg hh.le k)⟩
  · simp only [finiteDifference, if_neg hW, mem_Icc]
    exact ⟨le_refl _, by positivity⟩

lemma integrable_finiteDifference {W : Ω → ℝ} (hW : Measurable W)
    {θ h : ℝ} (hθ : 0 ≤ θ) (hh : 0 < h) (k : ℕ) :
    Integrable (fun ω => finiteDifference θ h k (W ω)) μ := by
  apply Integrable.of_bound (measurable_finiteDifference θ h k hW).aestronglyMeasurable
    (1/h^k)
  exact Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs,abs_of_nonneg (finiteDifference_bounds hθ hh k _).1]
    exact (finiteDifference_bounds hθ hh k _).2

lemma weightedMonomial_nonneg (θ : ℝ) (k : ℕ) (W : ℝ) :
    0 ≤ weightedMonomial θ k W := by
  by_cases hW : 0 < W
  · simp only [weightedMonomial, if_pos hW]
    positivity
  · simp only [weightedMonomial, if_neg hW, le_refl]

lemma integrable_weightedMonomial {W : Ω → ℝ} (hW : Measurable W)
    {θ : ℝ} (hθ : 0 < θ) (k : ℕ) :
    Integrable (fun ω => weightedMonomial θ k (W ω)) μ := by
  let h := θ/((k : ℝ)+1)
  have hh : 0 < h := div_pos hθ (by positivity)
  have hstart : 0 ≤ θ-(k : ℝ)*h := by
    have he : θ-(k : ℝ)*h=θ/((k : ℝ)+1) := by
      dsimp [h]
      field_simp [show (k : ℝ)+1 ≠ 0 by positivity]
      ring
    rw [he]
    positivity
  apply Integrable.mono' (integrable_finiteDifference μ hW hstart hh k)
    (measurable_weightedMonomial θ k hW).aestronglyMeasurable
  exact Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs,abs_of_nonneg (weightedMonomial_nonneg θ k _)]
    exact (finiteDifference_sandwich hh k (W ω)).2

end Finite

def signedDifference (k : ℕ) (f : ℕ → ℝ) : ℝ :=
  match k with
  | 0 => f 0
  | 1 => f 0-f 1
  | 2 => f 0-2*f 1+f 2
  | _ => f 0-3*f 1+3*f 2-f 3

lemma signedDifference_tendsto {f : ℕ → ℕ → ℝ} {g : ℕ → ℝ}
    (h : ∀ j, Tendsto (fun m => f m j) atTop (𝓝 (g j))) (k : ℕ) :
    Tendsto (fun m => signedDifference k (f m)) atTop (𝓝 (signedDifference k g)) := by
  cases k with
  | zero => exact h 0
  | succ k =>
    cases k with
    | zero => exact (h 0).sub (h 1)
    | succ k =>
      cases k with
      | zero => exact ((h 0).sub ((h 1).const_mul 2)).add (h 2)
      | succ k =>
        exact (((h 0).sub ((h 1).const_mul 3)).add ((h 2).const_mul 3)).sub (h 3)

lemma finiteDifference_zero (θ h W : ℝ) :
    finiteDifference θ h 0 W=strictLaplace θ W := by simp [finiteDifference,strictLaplace]

lemma integral_finiteDifference {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {W : Ω → ℝ} (hW : Measurable W)
    {θ h : ℝ} (hθ : 0 ≤ θ) (hh : 0 < h) {k : ℕ} (hk : k ≤ 3) :
    (∫ ω, finiteDifference θ h k (W ω) ∂μ)=
      signedDifference k (fun j => ∫ ω, strictLaplace (θ+(j : ℝ)*h) (W ω) ∂μ)/h^k := by
  have hI (j : ℕ) : Integrable (fun ω => strictLaplace (θ+(j : ℝ)*h) (W ω)) μ :=
    integrable_strictLaplace μ hW (by positivity)
  have hI0 : Integrable (fun ω => strictLaplace θ (W ω)) μ := by simpa using hI 0
  have hI1 : Integrable (fun ω => strictLaplace (θ+h) (W ω)) μ := by simpa using hI 1
  have hI2 : Integrable (fun ω => strictLaplace (θ+2*h) (W ω)) μ := by simpa using hI 2
  have hI3 : Integrable (fun ω => strictLaplace (θ+3*h) (W ω)) μ := by simpa using hI 3
  interval_cases k
  · simp [finiteDifference_zero,signedDifference]
  · simp_rw [finiteDifference_one]
    rw [integral_div,integral_sub hI0 hI1]
    simp [signedDifference]
  · simp_rw [finiteDifference_two]
    have htw : Integrable (fun ω => 2*strictLaplace (θ+h) (W ω)) μ := hI1.const_mul 2
    have hdiff : Integrable (fun ω => strictLaplace θ (W ω)-2*strictLaplace (θ+h) (W ω)) μ := hI0.sub htw
    rw [integral_div, integral_add hdiff hI2, integral_sub hI0 htw, integral_const_mul]
    simp [signedDifference]
  · simp_rw [finiteDifference_three]
    have hth1 : Integrable (fun ω => 3*strictLaplace (θ+h) (W ω)) μ := hI1.const_mul 3
    have hth2 : Integrable (fun ω => 3*strictLaplace (θ+2*h) (W ω)) μ := hI2.const_mul 3
    have hdiff : Integrable (fun ω => strictLaplace θ (W ω)-3*strictLaplace (θ+h) (W ω)) μ := hI0.sub hth1
    have hsum : Integrable (fun ω => strictLaplace θ (W ω)-3*strictLaplace (θ+h) (W ω)+3*strictLaplace (θ+2*h) (W ω)) μ := hdiff.add hth2
    rw [integral_div, integral_sub hsum hI3, integral_add hdiff hth2,
      integral_sub hI0 hth1, integral_const_mul, integral_const_mul]
    simp [signedDifference]

def reciprocalCoefficient (k : ℕ) (a ε : ℝ) : ℝ :=
  match k with
  | 0 => 1/a
  | 1 => 1/(a*(a+ε))
  | 2 => 2/(a*(a+ε)*(a+2*ε))
  | _ => 6/(a*(a+ε)*(a+2*ε)*(a+3*ε))

lemma reciprocalCoefficient_eq {k : ℕ} (hk : k ≤ 3) {a ε C : ℝ}
    (ha : 0 < a) (hε : 0 < ε) :
    signedDifference k (fun j => C/(a+(j : ℝ)*ε))/ε^k=C*reciprocalCoefficient k a ε := by
  have h0 : a ≠ 0 := ha.ne'
  have h1 : a+ε ≠ 0 := by positivity
  have h2 : a+2*ε ≠ 0 := by positivity
  have h3 : a+3*ε ≠ 0 := by positivity
  interval_cases k <;> simp [signedDifference,reciprocalCoefficient] <;>
    field_simp [h0,h1,h2,h3,hε.ne'] <;> ring

lemma reciprocalCoefficient_tendsto (a ε : ℕ → ℝ) {a0 : ℝ}
    (ha0 : 0 < a0) (ha : Tendsto a atTop (𝓝 a0))
    (hε : Tendsto ε atTop (𝓝 0)) {k : ℕ} (hk : k ≤ 3) :
    Tendsto (fun n => reciprocalCoefficient k (a n) (ε n)) atTop
      (𝓝 ((k.factorial : ℝ)/a0^(k+1))) := by
  have h1 : Tendsto (fun n => a n+ε n) atTop (𝓝 a0) := by simpa using ha.add hε
  have h2 : Tendsto (fun n => a n+2*ε n) atTop (𝓝 a0) := by
    simpa using ha.add (hε.const_mul 2)
  have h3 : Tendsto (fun n => a n+3*ε n) atTop (𝓝 a0) := by
    simpa using ha.add (hε.const_mul 3)
  interval_cases k
  · convert! (tendsto_const_nhds (x := (1:ℝ))).div ha ha0.ne' using 1
    simp
  · convert! (tendsto_const_nhds (x := (1:ℝ))).div (ha.mul h1) (by positivity : a0*a0 ≠ 0) using 1
    simp [Nat.factorial,pow_two]
  · convert! (tendsto_const_nhds (x := (2:ℝ))).div ((ha.mul h1).mul h2)
      (by positivity : a0*a0*a0 ≠ 0) using 1
    norm_num [reciprocalCoefficient,Nat.factorial,pow_succ]
  · convert! (tendsto_const_nhds (x := (6:ℝ))).div (((ha.mul h1).mul h2).mul h3)
      (by positivity : a0*a0*a0*a0 ≠ 0) using 1
    norm_num [reciprocalCoefficient,Nat.factorial,pow_succ]

theorem tendsto_of_parameter_sandwich (x : ℕ → ℝ) (L U : ℕ → ℕ → ℝ)
    (l u : ℕ → ℝ) (c : ℝ)
    (hL : ∀ n, Tendsto (L n) atTop (𝓝 (l n)))
    (hU : ∀ n, Tendsto (U n) atTop (𝓝 (u n)))
    (hb : ∀ n, ∀ᶠ m in atTop, L n m ≤ x m ∧ x m ≤ U n m)
    (hl : Tendsto l atTop (𝓝 c)) (hu : Tendsto u atTop (𝓝 c)) :
    Tendsto x atTop (𝓝 c) := by
  apply tendsto_order.2
  constructor
  · intro r hr
    obtain ⟨n,hn⟩ := (hl.eventually (Ioi_mem_nhds hr)).exists
    filter_upwards [(hL n).eventually (Ioi_mem_nhds hn),hb n] with m hm hbm
    exact hm.trans_le hbm.1
  · intro r hr
    obtain ⟨n,hn⟩ := (hu.eventually (Iio_mem_nhds hr)).exists
    filter_upwards [(hU n).eventually (Iio_mem_nhds hn),hb n] with m hm hbm
    exact hbm.2.trans_lt hm

section Asymptotics
variable {Ω : ℕ → Type u} [∀ m, MeasurableSpace (Ω m)]
  (μ : (m : ℕ) → Measure (Ω m)) [∀ m, IsProbabilityMeasure (μ m)]
  (W : (m : ℕ) → Ω m → ℝ) (θ s : ℕ → ℝ)

theorem finiteDifference_tendsto
    (hW : ∀ m, Measurable (W m)) (hθ : ∀ᶠ m in atTop, 0 < θ m)
    {C : ℝ} (hL : ∀ a : ℝ, 0 < a →
      Tendsto (fun m => (s m*θ m)*(∫ ω, strictLaplace (a*θ m) (W m ω) ∂μ m))
        atTop (𝓝 (C/a)))
    {k : ℕ} (hk : k ≤ 3) {a ε : ℝ} (ha : 0 < a) (hε : 0 < ε) :
    Tendsto (fun m => (s m*θ m^(k+1))*
      (∫ ω, finiteDifference (a*θ m) (ε*θ m) k (W m ω) ∂μ m))
      atTop (𝓝 (C*reciprocalCoefficient k a ε)) := by
  have ht := (signedDifference_tendsto (fun j => hL (a+(j : ℝ)*ε) (by positivity)) k).div_const (ε^k)
  rw [reciprocalCoefficient_eq hk ha hε] at ht
  apply ht.congr'
  filter_upwards [hθ] with m hθm
  rw [integral_finiteDifference (μ m) (hW m) (mul_pos ha hθm).le (mul_pos hε hθm) hk]
  have hfun : (fun j : ℕ => ∫ ω, strictLaplace (a*θ m+(j : ℝ)*(ε*θ m)) (W m ω) ∂μ m)=
      (fun j : ℕ => ∫ ω, strictLaplace ((a+(j : ℝ)*ε)*θ m) (W m ω) ∂μ m) := by
    funext j
    congr 1
    funext ω
    congr 1
    ring
  rw [hfun]
  interval_cases k <;> simp [signedDifference] <;> field_simp [hε.ne',hθm.ne']

theorem weightedMonomial_tendsto
    (hW : ∀ m, Measurable (W m))
    (hθ : ∀ᶠ m in atTop, 0 < θ m) (hs : ∀ᶠ m in atTop, 0 ≤ s m)
    {C : ℝ} (hL : ∀ a : ℝ, 0 < a →
      Tendsto (fun m => (s m*θ m)*(∫ ω, strictLaplace (a*θ m) (W m ω) ∂μ m))
        atTop (𝓝 (C/a)))
    {k : ℕ} (hk : k ≤ 3) :
    Tendsto (fun m => (s m*θ m^(k+1))*
      (∫ ω, weightedMonomial (θ m) k (W m ω) ∂μ m))
      atTop (𝓝 (C*(k.factorial : ℝ))) := by
  let ε : ℕ → ℝ := fun n => 1/(10*((n : ℝ)+1))
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hεsmall (n : ℕ) : ε n ≤ 1/10 := by
    dsimp [ε]
    apply (div_le_div_iff₀ (by positivity) (by norm_num)).2
    nlinarith [show (0 : ℝ) ≤ n by positivity]
  have hkR : (k : ℝ) ≤ 3 := by exact_mod_cast hk
  have ha (n : ℕ) : 0 < 1-(k : ℝ)*ε n := by
    have hmul := mul_le_mul (show (k : ℝ) ≤ 3 from hkR) (hεsmall n)
      (hε n).le (by norm_num : (0 : ℝ) ≤ 3)
    linarith
  have hεL : Tendsto ε atTop (𝓝 0) := by
    have hn : Tendsto (fun n : ℕ => (n:ℝ)+1) atTop atTop :=
      tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    exact (tendsto_const_nhds (x := (1:ℝ))).div_atTop
      (hn.const_mul_atTop (by norm_num : (0:ℝ)<10))
  let L : ℕ → ℕ → ℝ := fun n m => (s m*θ m^(k+1))*
    (∫ ω, finiteDifference (θ m) (ε n*θ m) k (W m ω) ∂μ m)
  let U : ℕ → ℕ → ℝ := fun n m => (s m*θ m^(k+1))*
    (∫ ω, finiteDifference ((1-(k : ℝ)*ε n)*θ m) (ε n*θ m) k (W m ω) ∂μ m)
  have hl (n : ℕ) : Tendsto (L n) atTop (𝓝 (C*reciprocalCoefficient k 1 (ε n))) := by
    simpa only [L,one_mul] using finiteDifference_tendsto μ W θ s hW hθ hL hk
      (by norm_num : (0 : ℝ) < 1) (hε n)
  have hu (n : ℕ) : Tendsto (U n) atTop
      (𝓝 (C*reciprocalCoefficient k (1-(k : ℝ)*ε n) (ε n))) :=
    finiteDifference_tendsto μ W θ s hW hθ hL hk (ha n) (hε n)
  have hb (n : ℕ) : ∀ᶠ m in atTop, L n m ≤
      (s m*θ m^(k+1))*(∫ ω, weightedMonomial (θ m) k (W m ω) ∂μ m) ∧
      (s m*θ m^(k+1))*(∫ ω, weightedMonomial (θ m) k (W m ω) ∂μ m) ≤ U n m := by
    filter_upwards [hθ,hs] with m hθm hsm
    have hhm := mul_pos (hε n) hθm
    have hwm := integrable_weightedMonomial (μ m) (hW m) hθm k
    have him := integrable_finiteDifference (μ m) (hW m) hθm.le hhm k
    have hum := integrable_finiteDifference (μ m) (hW m) (mul_pos (ha n) hθm).le hhm k
    have he : θ m-(k : ℝ)*(ε n*θ m)=(1-(k : ℝ)*ε n)*θ m := by ring
    constructor
    · apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact integral_mono him hwm (fun ω => (finiteDifference_sandwich hhm k (W m ω)).1)
    · apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply integral_mono hwm hum
      intro ω
      simpa only [he] using (finiteDifference_sandwich (θ := θ m) hhm k (W m ω)).2
  have hlL : Tendsto (fun n => C*reciprocalCoefficient k 1 (ε n)) atTop
      (𝓝 (C*(k.factorial : ℝ))) := by
    simpa only [one_pow,div_one] using
      (reciprocalCoefficient_tendsto (fun _ => 1) ε (by norm_num : (0 : ℝ)<1)
        tendsto_const_nhds hεL hk).const_mul C
  have huL : Tendsto (fun n => C*reciprocalCoefficient k (1-(k : ℝ)*ε n) (ε n))
      atTop (𝓝 (C*(k.factorial : ℝ))) := by
    have hstartL : Tendsto (fun n => 1-(k : ℝ)*ε n) atTop (𝓝 1) := by
      simpa only [mul_zero,sub_zero] using tendsto_const_nhds.sub (hεL.const_mul (k : ℝ))
    simpa only [one_pow,div_one] using
      (reciprocalCoefficient_tendsto (fun n => 1-(k : ℝ)*ε n) ε
        (by norm_num : (0 : ℝ)<1) hstartL hεL hk).const_mul C
  exact tendsto_of_parameter_sandwich _ L U _ _ _ hl hu hb hlL huL

end Asymptotics

theorem actual_centered_tilt_weighted_moments
    {Ω : ℕ → Type u} [∀ m, MeasurableSpace (Ω m)]
    (μ : (m : ℕ) → Measure (Ω m)) [∀ m, IsProbabilityMeasure (μ m)]
    (X : (m : ℕ) → Ω m → ℝ) (u θ : ℕ → ℝ) (N : ℕ → ℕ)
    (hX : ∀ m, Measurable (X m))
    (hb : ∀ m, ∀ᵐ ω ∂μ m, X m ω ∈ Icc (0 : ℝ) 1)
    (hN : Tendsto N atTop atTop) {v : ℝ} (hv : 0 < v)
    (hvar : Tendsto (fun m => variance (X m)
      ((μ m).tilted (fun ω => u m*X m ω))) atTop (𝓝 v))
    (hθ : Tendsto θ atTop (𝓝 0))
    (hwindow : Tendsto (fun m => θ m*Real.sqrt ((N m : ℝ)*variance (X m)
      ((μ m).tilted (fun ω => u m*X m ω)))) atTop atTop)
    {k : ℕ} (hk : k ≤ 3) :
    Tendsto (fun m =>
      (Real.sqrt ((N m : ℝ)*variance (X m) ((μ m).tilted (fun ω => u m*X m ω)))*θ m^(k+1))*
      (∫ r, weightedMonomial (θ m) k
        ((N m : ℝ)*(∫ ω, X m ω ∂(μ m).tilted (fun ω => u m*X m ω))-
          iidSum (X m) (N m) r)
        ∂(Measure.pi (fun _ : Fin (N m) => μ m)).tilted
          (fun r => u m*iidSum (X m) (N m) r)))
      atTop (𝓝 (φ0*(k.factorial : ℝ))) := by
  let P := fun m => (Measure.pi (fun _ : Fin (N m) => μ m)).tilted
    (fun r => u m*iidSum (X m) (N m) r)
  let s := fun m => Real.sqrt ((N m : ℝ)*variance (X m)
    ((μ m).tilted (fun ω => u m*X m ω)))
  let W := fun m r => (N m : ℝ)*(∫ ω, X m ω ∂(μ m).tilted (fun ω => u m*X m ω))-
    iidSum (X m) (N m) r
  haveI : ∀ m, IsProbabilityMeasure (P m) := fun m =>
    isProbabilityMeasure_tilted_iidSum (μ m) (hX m) (hb m) (u m) (N m)
  have hθpos : ∀ᶠ m in atTop, 0 < θ m := by
    filter_upwards [hwindow.eventually_gt_atTop 0] with m hm
    exact pos_of_mul_pos_left hm (Real.sqrt_nonneg _)
  apply weightedMonomial_tendsto P W θ s
    (fun m => measurable_const.sub (measurable_iidSum (hX m) (N m))) hθpos
    (Eventually.of_forall fun m => Real.sqrt_nonneg _) ?_ hk
  intro a ha
  have hlim := actual_centered_tilt_Laplace μ X u (fun m => a*θ m) N hX hb hN hv hvar
    (by simpa using hθ.const_mul a)
    (by simpa only [mul_assoc] using hwindow.const_mul_atTop ha)
  have he := hlim.div_const a
  apply he.congr'
  exact Eventually.of_forall fun m => by
    dsimp only [P,W,s]
    field_simp [ha.ne']

end FCAppendix.Affine.Uniform06.EntryWeightedLaplace
