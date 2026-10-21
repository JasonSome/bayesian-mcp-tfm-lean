import FCAppendix.Affine.Uniform06.EntryCentralSampling

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.EntryCentralReplacement
open MeasureTheory ProbabilityTheory Set Filter Topology
open FCAppendix.Affine.WeightedSampling
open FCAppendix.Affine.Uniform06.WeightedMoments
open FCAppendix.Affine.Uniform06.EntrySamplingLaw
open FCAppendix.Affine.Uniform06.EntryCentralSampling
open scoped BigOperators

lemma tendsto_zero_of_parameter_bound (f g h : ℕ → ℝ) {C : ℝ}
    (hC : 0 ≤ C) (hf : ∀ m, 0 ≤ f m)
    (hg : Tendsto g atTop (𝓝 0)) (hh : Tendsto h atTop (𝓝 0))
    (hb : ∀ δ : ℝ, 0 < δ → ∀ᶠ m in atTop, f m ≤ g m+δ*C+h m/δ) :
    Tendsto f atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let δ := ε/(4*(C+1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδC : δ*C < ε/4 := by
    have hd : 0 < 4*(C+1) := by positivity
    have he : δ*C=ε*C/(4*(C+1)) := by dsimp [δ]; ring
    rw [he]
    apply (div_lt_iff₀ hd).mpr
    nlinarith
  have hgε := hg.eventually (eventually_lt_nhds (show 0 < ε/4 by positivity))
  have hhε := (hh.div_const δ).eventually (eventually_lt_nhds (show (0:ℝ)/δ < ε/4 by rw [zero_div]; positivity))
  filter_upwards [hb δ hδ,hgε,hhε] with m hm hgm hhm
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (hf m)]
  linarith

section Finite
variable {Ω ι : Type*} [MeasurableSpace Ω]
  [Fintype ι] [DecidableEq ι] [Nonempty ι]

lemma bounded_integrable_pow (μ : Measure Ω) [IsProbabilityMeasure μ]
    {f : Ω → ℝ} (hf : Measurable f) {C : ℝ} (hb : ∀ ω, |f ω| ≤ C) (k : ℕ) :
    Integrable (fun ω => (f ω)^k) μ := by
  apply Integrable.of_bound (hf.pow_const k).aestronglyMeasurable (C^k)
  exact Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs,abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hb ω) k

lemma integral_dependent_product (μ : Measure Ω) [IsProbabilityMeasure μ]
    {Z e : Ω → ℝ} (hZ : Measurable Z) (he : Measurable e)
    {C D δ : ℝ} (hZb : ∀ ω, |Z ω| ≤ C) (heb : ∀ ω, |e ω| ≤ D)
    (hδ : 0 < δ) :
    (∫ ω, (Z ω)^2*(e ω)^2 ∂μ) ≤
      δ*(∫ ω, (Z ω)^4 ∂μ)+(∫ ω, (e ω)^4 ∂μ)/(4*δ) := by
  have hI : Integrable (fun ω => (Z ω)^2*(e ω)^2) μ := by
    apply Integrable.of_bound ((hZ.pow_const 2).mul (he.pow_const 2)).aestronglyMeasurable (C^2*D^2)
    exact Eventually.of_forall fun ω => by
      change |Z ω^2*e ω^2| ≤ C^2*D^2
      rw [abs_mul,abs_pow,abs_pow]
      exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) (hZb ω) 2)
        (pow_le_pow_left₀ (abs_nonneg _) (heb ω) 2) (sq_nonneg _) (sq_nonneg _)
  have hZ4 := bounded_integrable_pow μ hZ hZb 4
  have he4 := bounded_integrable_pow μ he heb 4
  have hh := integral_mono hI ((hZ4.const_mul δ).add (he4.div_const (4*δ)))
    (fun ω => dependent_product_bound (Z := Z ω) (e := e ω) hδ)
  change (∫ ω, Z ω^2*e ω^2 ∂μ) ≤
    (∫ ω, δ*Z ω^4+e ω^4/(4*δ) ∂μ) at hh
  simpa only [integral_add (hZ4.const_mul δ) (he4.div_const (4*δ)),
    integral_const_mul,integral_div] using hh

omit [MeasurableSpace Ω] in
lemma guardedSample_abs_le (w : Ω → Weights ι) (h : Ω → ι → ℝ) (d : Ω → ℕ)
    {A c h0 : ℝ} (hA : 0 ≤ A) (hh : ∀ ω i, |h ω i| ≤ A) (h0b : |h0| ≤ A)
    (x : Ω × unitInterval) : |guardedSample w h d c h0 x| ≤ A*d x.1 := by
  unfold guardedSample
  split_ifs
  · simpa only [sampled,mul_comm] using abs_selectedSum_le hA (hh x.1) _ _
  · rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg _)]
    nlinarith [mul_le_mul_of_nonneg_left h0b (Nat.cast_nonneg (d x.1))]

lemma normalized_count_fourth (μ : Measure Ω) [IsProbabilityMeasure μ]
    {N : ℕ} (hN : 0 < N) (Y : Fin N → Ω → ℝ)
    (hmY : ∀ i, Measurable (Y i)) (hbY : ∀ i, ∀ᵐ ω ∂μ, |Y i ω| ≤ 1)
    (hzY : ∀ i, ∫ ω, Y i ω ∂μ=0) (hiY : iIndepFun Y μ)
    (d : Ω → ℕ) (hcount : ∀ ω, (d ω : ℝ)=|∑ i, Y i ω|) :
    (∫ ω, ((d ω : ℝ)/Real.sqrt (N : ℝ))^4 ∂μ) ≤
      2*FCAppendix.Probability.gaussianMomentConstant 4 2 := by
  have hr : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hN)
  have he (ω : Ω) : ((d ω : ℝ)/Real.sqrt (N : ℝ))^4=
      (EntryUI.normalizedSum Y ω)^4 := by
    have hh : (d ω : ℝ)/Real.sqrt (N : ℝ)=|EntryUI.normalizedSum Y ω| := by
      rw [hcount,EntryUI.normalizedSum,abs_div,abs_of_pos hr]
    rw [hh,show (4:ℕ)=2*2 by norm_num,pow_mul,pow_mul,sq_abs]
  simpa only [he] using EntryUI.normalizedSum_fourth_moment μ hN Y hmY hbY hzY hiY

theorem actual_centered_normalized_second (μ : Measure Ω) [IsProbabilityMeasure μ]
    {N : ℕ} (hN : 0 < N) (Y : Fin N → Ω → ℝ)
    (hmY : ∀ i, Measurable (Y i)) (hbY : ∀ i, ∀ᵐ ω ∂μ, |Y i ω| ≤ 1)
    (hzY : ∀ i, ∫ ω, Y i ω ∂μ=0) (hiY : iIndepFun Y μ)
    (w : Ω → Weights ι) (h : Ω → ι → ℝ) (d : Ω → ℕ)
    (hw : Measurable w) (hmh : Measurable h) (hd : Measurable d)
    {A c : ℝ} (hA : 0 ≤ A) (hc : 0 < c) (hh : ∀ ω i, |h ω i| ≤ A)
    (hD : ∀ ω, d ω ≤ N) (hcount : ∀ ω, (d ω : ℝ)=|∑ i, Y i ω|) :
    (∫ x, (centeredGuardedSample w h d (c*N) x/Real.sqrt (N : ℝ))^2 ∂μ.prod volume) ≤
      8*A^2*(1+2*FCAppendix.Probability.gaussianMomentConstant 4 2)/Real.sqrt (N : ℝ)+
      32*A^2*(2*FCAppendix.Probability.gaussianMomentConstant 4 2)/(c^2*N) := by
  let K := 2*FCAppendix.Probability.gaussianMomentConstant 4 2
  have hNr : (0:ℝ)< N := by exact_mod_cast hN
  have hr : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNr
  have hm := actual_guarded_sampling_second μ w h d hw hmh hd hA (mul_pos hc hNr) hh N hD
  have hdM := physical_draw_moments μ hN Y hmY hbY hzY hiY d hd hD hcount
  have hb : (∫ x, (centeredGuardedSample w h d (c*N) x)^2 ∂μ.prod volume) ≤
      8*A^2*(Real.sqrt (N : ℝ)*(1+K))+32*A^2/(c*N)^2*((N : ℝ)^2*K) :=
    hm.trans (add_le_add
      (mul_le_mul_of_nonneg_left hdM.1 (by positivity))
      (mul_le_mul_of_nonneg_left hdM.2 (by positivity)))
  have he (x : Ω × unitInterval) :
      (centeredGuardedSample w h d (c*N) x/Real.sqrt (N : ℝ))^2=
        (centeredGuardedSample w h d (c*N) x)^2/(N : ℝ) := by
    rw [div_pow,Real.sq_sqrt hNr.le]
  simp_rw [he]
  rw [integral_div]
  apply (div_le_div_of_nonneg_right hb hNr.le).trans_eq
  change (8*A^2*(Real.sqrt (N : ℝ)*(1+K))+32*A^2/(c*N)^2*((N : ℝ)^2*K))/(N : ℝ)=
    8*A^2*(1+K)/Real.sqrt (N : ℝ)+32*A^2*K/(c^2*N)
  have he : (8*A^2*(Real.sqrt (N : ℝ)*(1+K))+32*A^2/(c*N)^2*((N : ℝ)^2*K))/(N : ℝ)=
      8*A^2*(1+K)*(Real.sqrt (N : ℝ)/(N : ℝ))+32*A^2*K/(c^2*N) := by
    field_simp [hc.ne',hNr.ne']
  have hrN : Real.sqrt (N : ℝ)/(N : ℝ)=(Real.sqrt (N : ℝ))⁻¹ := by
    field_simp [hNr.ne',hr.ne']
    nlinarith [Real.sq_sqrt hNr.le]
  rw [he,hrN]
  ring

omit [MeasurableSpace Ω] in
lemma replacement_square_pointwise (w : Ω → Weights ι) (h : Ω → ι → ℝ) (d : Ω → ℕ)
    (c h0 R : ℝ) (x : Ω × unitInterval) :
    ((guardedSample w h d c h0 x-(d x.1 : ℝ)*h0)/R)^2 ≤
      2*(centeredGuardedSample w h d c x/R)^2+
      2*((d x.1 : ℝ)/R)^2*(guardedMean w h c h0 x.1-h0)^2 := by
  rw [guarded_decomposition,add_div]
  have he : ((d x.1 : ℝ)*(guardedMean w h c h0 x.1-h0)/R)=
      ((d x.1 : ℝ)/R)*(guardedMean w h c h0 x.1-h0) := by ring
  rw [he]
  nlinarith [sq_nonneg (centeredGuardedSample w h d c x/R-
    ((d x.1 : ℝ)/R)*(guardedMean w h c h0 x.1-h0))]

end Finite

section Arrays
variable {Ω ι : ℕ → Type*} [∀ m, MeasurableSpace (Ω m)]
  [∀ m, Fintype (ι m)] [∀ m, DecidableEq (ι m)] [∀ m, Nonempty (ι m)]
  (μ : (m : ℕ) → Measure (Ω m)) [∀ m, IsProbabilityMeasure (μ m)]

theorem dependent_profile_error_tendsto
    (N : ℕ → ℕ) (hN : ∀ m, 0 < N m)
    (Y : (m : ℕ) → Fin (N m) → Ω m → ℝ)
    (hmY : ∀ m i, Measurable (Y m i))
    (hbY : ∀ m i, ∀ᵐ ω ∂μ m, |Y m i ω| ≤ 1)
    (hzY : ∀ m i, ∫ ω, Y m i ω ∂μ m=0)
    (hiY : ∀ m, iIndepFun (Y m) (μ m))
    (d : (m : ℕ) → Ω m → ℕ) (hd : ∀ m, Measurable (d m))
    (hD : ∀ m ω, d m ω ≤ N m)
    (hcount : ∀ m ω, (d m ω : ℝ)=|∑ i, Y m i ω|)
    (e : (m : ℕ) → Ω m → ℝ) (he : ∀ m, Measurable (e m))
    {C : ℝ} (hC : 0 ≤ C) (heb : ∀ m ω, |e m ω| ≤ C)
    (hL1 : Tendsto (fun m => ∫ ω, |e m ω| ∂μ m) atTop (𝓝 0)) :
    Tendsto (fun m => ∫ ω, ((d m ω : ℝ)/Real.sqrt (N m : ℝ))^2*(e m ω)^2 ∂μ m)
      atTop (𝓝 0) := by
  let K := 2*FCAppendix.Probability.gaussianMomentConstant 4 2
  have h4 := EntryEmpiricalRatio.bounded_error_fourth_tendsto μ e he hC
    (fun m => Eventually.of_forall (heb m)) hL1
  have hK : 0 ≤ K := by
    have hb := normalized_count_fourth (μ 0) (hN 0) (Y 0) (hmY 0) (hbY 0)
      (hzY 0) (hiY 0) (d 0) (hcount 0)
    exact (integral_nonneg fun _ => by positivity).trans hb
  apply tendsto_zero_of_parameter_bound _ (fun _ => 0)
    (fun m => (∫ ω, (e m ω)^4 ∂μ m)/4) hK
    (fun _ => integral_nonneg fun _ => by positivity) tendsto_const_nhds
    (by simpa using h4.div_const 4)
  intro δ hδ
  exact Eventually.of_forall fun m => by
    have hr : 0 < Real.sqrt (N m : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hN m)
    have hzbound (ω : Ω m) : |(d m ω : ℝ)/Real.sqrt (N m : ℝ)| ≤
        (N m : ℝ)/Real.sqrt (N m : ℝ) := by
      rw [abs_div,abs_of_pos hr,abs_of_nonneg (Nat.cast_nonneg _)]
      exact div_le_div_of_nonneg_right (by exact_mod_cast hD m ω) hr.le
    have hb := integral_dependent_product (μ m) (((measurable_of_countable (fun n : ℕ => (n:ℝ))).comp (hd m)).div_const _) (he m)
      hzbound (heb m) hδ
    have hz4 := normalized_count_fourth (μ m) (hN m) (Y m) (hmY m) (hbY m)
      (hzY m) (hiY m) (d m) (hcount m)
    have hh := hb.trans (add_le_add (mul_le_mul_of_nonneg_left hz4 hδ.le) le_rfl)
    simpa only [K,Function.comp_apply,zero_add,div_div] using! hh

theorem actual_guarded_replacement_L2
    (N : ℕ → ℕ) (hNp : ∀ m, 0 < N m) (hN : Tendsto N atTop atTop)
    (Y : (m : ℕ) → Fin (N m) → Ω m → ℝ)
    (hmY : ∀ m i, Measurable (Y m i))
    (hbY : ∀ m i, ∀ᵐ ω ∂μ m, |Y m i ω| ≤ 1)
    (hzY : ∀ m i, ∫ ω, Y m i ω ∂μ m=0)
    (hiY : ∀ m, iIndepFun (Y m) (μ m))
    (w : (m : ℕ) → Ω m → Weights (ι m)) (h : (m : ℕ) → Ω m → ι m → ℝ)
    (d : (m : ℕ) → Ω m → ℕ)
    (hw : ∀ m, Measurable (w m)) (hmh : ∀ m, Measurable (h m))
    (hd : ∀ m, Measurable (d m))
    {A c h0 : ℝ} (hA : 0 ≤ A) (hc : 0 < c)
    (hh : ∀ m ω i, |h m ω i| ≤ A) (h0b : |h0| ≤ A)
    (hD : ∀ m ω, d m ω ≤ N m)
    (hcount : ∀ m ω, (d m ω : ℝ)=|∑ i, Y m i ω|)
    (hMean : Tendsto (fun m => ∫ ω, |guardedMean (w m) (h m) (c*N m) h0 ω-h0| ∂μ m)
      atTop (𝓝 0)) :
    Tendsto (fun m => ∫ x,
      ((guardedSample (w m) (h m) (d m) (c*N m) h0 x-(d m x.1 : ℝ)*h0)/
        Real.sqrt (N m : ℝ))^2 ∂(μ m).prod volume) atTop (𝓝 0) := by
  let K := 2*FCAppendix.Probability.gaussianMomentConstant 4 2
  have hRoot : Tendsto (fun m => Real.sqrt (N m : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp hN)
  have hC0 : Tendsto (fun m => ∫ x,
      (centeredGuardedSample (w m) (h m) (d m) (c*N m) x/Real.sqrt (N m : ℝ))^2
        ∂(μ m).prod volume) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => integral_nonneg fun _ => sq_nonneg _)
      (fun m => actual_centered_normalized_second (μ m) (hNp m) (Y m) (hmY m)
        (hbY m) (hzY m) (hiY m) (w m) (h m) (d m) (hw m) (hmh m) (hd m)
        hA hc (hh m) (hD m) (hcount m))
    simpa only [add_zero,Function.comp_apply] using! (tendsto_const_nhds.div_atTop hRoot).add
      (tendsto_const_nhds.div_atTop
        ((tendsto_natCast_atTop_atTop.comp hN).const_mul_atTop (sq_pos_of_pos hc)))
  let e := fun m ω => guardedMean (w m) (h m) (c*N m) h0 ω-h0
  have he m : Measurable (e m) := (measurable_guardedMean (w m) (h m) (hw m) (hmh m) _ _).sub_const _
  have heb m ω : |e m ω| ≤ 2*A := by
    have hNr : (0:ℝ) < N m := by exact_mod_cast hNp m
    have hg := guardedMean_abs_le (w m) (h m)
      (show 0 < c*(N m : ℝ) by positivity) (hh m) h0b ω
    exact (abs_sub _ _).trans (by linarith)
  have hE0 := dependent_profile_error_tendsto μ N hNp Y hmY hbY hzY hiY d hd hD hcount
    e he (by positivity : 0 ≤ 2*A) heb hMean
  apply squeeze_zero (fun _ => integral_nonneg fun _ => sq_nonneg _) ?_
    (by simpa using (hC0.const_mul 2).add (hE0.const_mul 2))
  intro m
  let P := (μ m).prod (volume : Measure unitInterval)
  have hNr : (0:ℝ) < N m := by exact_mod_cast hNp m
  have hr : 0 < Real.sqrt (N m : ℝ) := Real.sqrt_pos.mpr hNr
  have hci : Integrable (fun x =>
      (centeredGuardedSample (w m) (h m) (d m) (c*N m) x/Real.sqrt (N m : ℝ))^2) P := by
    apply bounded_integrable_pow P
      ((measurable_centeredGuardedSample (w m) (h m) (d m) (hw m) (hmh m) (hd m) _).div_const _)
      (C := 2*A*N m/Real.sqrt (N m : ℝ))
    intro x
    rw [abs_div,abs_of_pos hr]
    exact div_le_div_of_nonneg_right
      ((centeredGuardedSample_abs_le (w m) (h m) (d m) hA (by positivity) (hh m) x).trans
        (mul_le_mul_of_nonneg_left (by exact_mod_cast hD m x.1) (by positivity))) hr.le
  have hei : Integrable (fun ω => ((d m ω : ℝ)/Real.sqrt (N m : ℝ))^2*(e m ω)^2) (μ m) := by
    apply Integrable.of_bound
      (((((measurable_of_countable (fun n : ℕ => (n:ℝ))).comp (hd m)).div_const _).pow_const 2).mul ((he m).pow_const 2)).aestronglyMeasurable
      (((N m : ℝ)/Real.sqrt (N m : ℝ))^2*(2*A)^2)
    exact Eventually.of_forall fun ω => by
      change |((d m ω:ℝ)/Real.sqrt (N m:ℝ))^2*(e m ω)^2| ≤ _
      rw [abs_mul,abs_pow,abs_pow,abs_div,
        abs_of_pos hr,abs_of_nonneg (Nat.cast_nonneg _)]
      exact mul_le_mul (pow_le_pow_left₀ (by positivity)
        (div_le_div_of_nonneg_right (by exact_mod_cast hD m ω) hr.le) 2)
        (pow_le_pow_left₀ (abs_nonneg _) (heb m ω) 2) (sq_nonneg _) (sq_nonneg _)
  have hep : Integrable (fun x : Ω m × unitInterval =>
      ((d m x.1 : ℝ)/Real.sqrt (N m : ℝ))^2*(e m x.1)^2) P :=
    (measurePreserving_fst (μ := μ m) (ν := (volume : Measure unitInterval))).integrable_comp_of_integrable hei
  have hli : Integrable (fun x =>
      ((guardedSample (w m) (h m) (d m) (c*N m) h0 x-(d m x.1 : ℝ)*h0)/
        Real.sqrt (N m : ℝ))^2) P := by
    apply Integrable.mono' ((hci.const_mul 2).add (hep.const_mul 2))
      ((((measurable_guardedSample (w m) (h m) (d m) (hw m) (hmh m) (hd m) _ _).sub
        ((((measurable_of_countable (fun n : ℕ => (n:ℝ))).comp (hd m)).comp measurable_fst).mul_const h0)).div_const _).pow_const 2).aestronglyMeasurable
    exact Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      change ((guardedSample (w m) (h m) (d m) (c*N m) h0 x-
        (d m x.1:ℝ)*h0)/Real.sqrt (N m:ℝ))^2 ≤ _
      dsimp only [Pi.add_apply,e]
      nlinarith only [replacement_square_pointwise (w m) (h m) (d m)
        (c*N m) h0 (Real.sqrt (N m : ℝ)) x]
  have hbnd := integral_mono hli ((hci.const_mul 2).add (hep.const_mul 2))
    (fun x => by
      dsimp only [Pi.add_apply,e]
      nlinarith only [replacement_square_pointwise (w m) (h m) (d m)
        (c*N m) h0 (Real.sqrt (N m : ℝ)) x])
  change (∫ x, ((guardedSample (w m) (h m) (d m) (c*N m) h0 x-
      (d m x.1:ℝ)*h0)/Real.sqrt (N m:ℝ))^2 ∂P) ≤
    (∫ x, 2*(centeredGuardedSample (w m) (h m) (d m) (c*N m) x/Real.sqrt (N m:ℝ))^2+
      2*(((d m x.1:ℝ)/Real.sqrt (N m:ℝ))^2*(e m x.1)^2) ∂P) at hbnd
  rw [integral_add (hci.const_mul 2) (hep.const_mul 2),integral_const_mul,integral_const_mul] at hbnd
  have hpi : (∫ x : Ω m × unitInterval,
      ((d m x.1 : ℝ)/Real.sqrt (N m : ℝ))^2*(e m x.1)^2 ∂P)=
      ∫ ω, ((d m ω : ℝ)/Real.sqrt (N m : ℝ))^2*(e m ω)^2 ∂μ m := by
    dsimp only [P]
    rw [integral_prod _ hep]
    simp only [integral_const,probReal_univ,one_smul]
  rw [hpi] at hbnd
  exact hbnd

end Arrays
end FCAppendix.Affine.Uniform06.EntryCentralReplacement
