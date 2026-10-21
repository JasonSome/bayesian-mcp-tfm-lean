import FCAppendix.Affine.Uniform06.SampledCellDomination

noncomputable section
namespace FCAppendix.Affine.Uniform06.SampledSafeLimit

open Set MeasureTheory Filter
open scoped Topology BigOperators
open FCAppendix.Affine.WeightedSampling
open FiniteSampledLaplace SampledCellDomination RareEmpiricalReplacement
open PathNumerator MixedIntervalLLT

variable {Ω : Type*} [MeasurableSpace Ω]

omit [MeasurableSpace Ω] in
lemma sampledRow_nonneg {N : ℕ} [Nonempty (Fin N)]
    (X h w : Ω → ℝ) (Y : Ω → ℤ) (hw : ∀ x,w x ∈ Icc (0:ℝ) 1)
    (cap θ : ℝ) (y : ℤ) (r k : ℕ) (ω : Fin N → Ω) :
    0 ≤ sampledRow X h w Y hw cap θ y r k ω :=
  FiniteLaw.expect_nonneg _ (fun p => tupleTest_nonneg X h Y cap θ y r ω (tuple k p))

omit [MeasurableSpace Ω] in
lemma safe_le_sampled {N : ℕ} [Nonempty (Fin N)]
    (X h w : Ω → ℝ) (Y : Ω → ℤ) (hw : ∀ x,w x ∈ Icc (0:ℝ) 1)
    (cap θ : ℝ) (y : ℤ) (r k : ℕ) (ω : Fin N → Ω) :
    safeRow X h w Y hw cap θ y r k ω ≤ sampledRow X h w Y hw cap θ y r k ω := by
  unfold safeRow
  split_ifs
  · rfl
  · exact sampledRow_nonneg _ _ _ _ _ _ _ _ _ _ _

lemma polynomial_sampled_ae (μ : Measure Ω) [IsProbabilityMeasure μ]
    {N : ℕ} [Nonempty (Fin N)] (hN : 0 < N)
    (X h w : Ω → ℝ) (Y : Ω → ℤ) (hw : ∀ x,w x ∈ Icc (0:ℝ) 1)
    (hp : ∀ᵐ x ∂μ,0 ≤ X x ∧ 0 ≤ h x)
    {cap θ : ℝ} (hc : cap ≤ (N:ℝ)) (ht : 0 ≤ θ) (y : ℤ) (r k : ℕ) :
    ∀ᵐ ω ∂Measure.pi (fun _ : Fin N => μ),
      sampledRow X h w Y hw cap θ y r k ω ∈ Icc (0:ℝ) ((N:ℝ)^r) ∧
      safeRow X h w Y hw cap θ y r k ω ∈ Icc (0:ℝ) ((N:ℝ)^r) := by
  have he (j : Fin N) := (measurePreserving_eval (fun _ : Fin N => μ) j).quasiMeasurePreserving.ae hp
  filter_upwards [ae_all_iff.mpr he] with ω hω
  have hb := (row_polynomial_bounds X h w Y hw cap θ y r k ω hN
    (fun j => (hω j).1) (fun j => (hω j).2) hc ht).1
  exact ⟨hb,⟨safeRow_nonneg _ _ _ _ _ _ _ _ _ _ _,
    (safe_le_sampled _ _ _ _ _ _ _ _ _ _ _).trans hb.2⟩⟩

omit [MeasurableSpace Ω] in
lemma safe_difference {N : ℕ} [Nonempty (Fin N)]
    (X h w : Ω → ℝ) (Y : Ω → ℤ) (hw : ∀ x,w x ∈ Icc (0:ℝ) 1)
    (cap θ : ℝ) (y : ℤ) (r k : ℕ) (ω : Fin N → Ω) :
    sampledRow X h w Y hw cap θ y r k ω-safeRow X h w Y hw cap θ y r k ω=
      {ω : Fin N → Ω | totalWeight (rowWeights w hw ω) ≤ (k:ℝ)}.indicator
        (sampledRow X h w Y hw cap θ y r k) ω := by
  by_cases hW : (k:ℝ) < totalWeight (rowWeights w hw ω)
  · simp only [safeRow,if_pos hW,sub_self,indicator_apply,mem_setOf_eq,if_neg (not_le.mpr hW)]
  · simp only [safeRow,if_neg hW,sub_zero,indicator_apply,mem_setOf_eq,if_pos (le_of_not_gt hW)]

theorem weight_failure_probability
    (μ : ℕ → Measure Ω) [∀ n,IsProbabilityMeasure (μ n)]
    (N : ℕ → ℕ) (hNpos : ∀ n,0 < N n) (hN : Tendsto N atTop atTop)
    (w : ℕ → Ω → ℝ) (hw : ∀ n,Measurable (w n))
    (hbw : ∀ n x,w n x ∈ Icc (0:ℝ) 1) (k : ℕ)
    {z : ℝ} (hz : 0 < z)
    (hmean : Tendsto (fun n => ∫ x,w n x ∂μ n) atTop (𝓝 z)) :
    ∀ᶠ n in atTop,(Measure.pi (fun _ : Fin (N n) => μ n)).real
      {ω : Fin (N n) → Ω | totalWeight (rowWeights (w n) (hbw n) ω) ≤ (k:ℝ)} ≤
        Real.exp (-(2*(z/4)^2)*(N n:ℝ)) := by
  have hreal : Tendsto (fun n => (N n:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hN
  have hinv : Tendsto (fun n => (N n:ℝ)⁻¹) atTop (𝓝 (0:ℝ)) :=
    tendsto_inv_atTop_zero.comp hreal
  have hk : ∀ᶠ n in atTop,(k:ℝ)/(N n:ℝ) < z/4 := by
    have ht : Tendsto (fun n => (k:ℝ)/(N n:ℝ)) atTop (𝓝 (0:ℝ)) := by
      simpa only [div_eq_mul_inv,mul_zero] using hinv.const_mul (k:ℝ)
    exact ht.eventually (Iio_mem_nhds (div_pos hz (by norm_num)))
  have hm := hmean.eventually (Ioi_mem_nhds (show z/2 < z by linarith))
  filter_upwards [hk,hm] with n hkn hmn
  have hNr : 0 < (N n:ℝ) := Nat.cast_pos.mpr (hNpos n)
  have hsub : {ω : Fin (N n) → Ω | totalWeight (rowWeights (w n) (hbw n) ω) ≤ (k:ℝ)} ⊆
      {ω | z/4 ≤ (∫ x,w n x ∂μ n)-empirical (w n) (N n) ω} := by
    intro ω hω
    have hwm : empirical (w n) (N n) ω ≤ (k:ℝ)/(N n:ℝ) :=
      div_le_div_of_nonneg_right hω hNr.le
    change z/4 ≤ (∫ x,w n x ∂μ n)-empirical (w n) (N n) ω
    linarith
  have hh := FCAppendix.Probability.iid_empiricalMean_lower_tail_le (μ n)
    (hw n).aemeasurable (ae_of_all _ (hbw n)) (N n) (hNpos n)
    (show 0 ≤ z/4 by positivity)
  have he : -2*(N n:ℝ)*(z/4)^2=-(2*(z/4)^2)*(N n:ℝ) := by ring
  rw [he] at hh
  exact (measureReal_mono hsub).trans hh

theorem fixed_safe_difference
    (μ : ℕ → Measure Ω) [∀ n,IsProbabilityMeasure (μ n)]
    (N : ℕ → ℕ) [∀ n,Nonempty (Fin (N n))]
    (hNpos : ∀ n,0 < N n) (hN : Tendsto N atTop atTop)
    (X h w : ℕ → Ω → ℝ) (Y : ℕ → Ω → ℤ)
    (hX : ∀ n,Measurable (X n)) (hh : ∀ n,Measurable (h n))
    (hw : ∀ n,Measurable (w n)) (hY : ∀ n,Measurable (Y n))
    (hbw : ∀ n x,w n x ∈ Icc (0:ℝ) 1)
    (hpositive : ∀ n,∀ᵐ x ∂μ n,0 ≤ X n x ∧ 0 ≤ h n x)
    (cap θ : ℕ → ℝ) (hcap : ∀ n,cap n ≤ (N n:ℝ)) (hθ : ∀ n,0 ≤ θ n)
    (y : ℤ) (r k : ℕ) {z : ℝ} (hz : 0 < z)
    (hmean : Tendsto (fun n => ∫ x,w n x ∂μ n) atTop (𝓝 z)) :
    Tendsto (fun n => (N n:ℝ)*∫ ω : Fin (N n) → Ω,
      sampledRow (X n) (h n) (w n) (Y n) (hbw n) (cap n) (θ n) y r k ω-
      safeRow (X n) (h n) (w n) (Y n) (hbw n) (cap n) (θ n) y r k ω
        ∂Measure.pi (fun _ : Fin (N n) => μ n)) atTop (𝓝 0) := by
  let T : (n : ℕ) → (Fin (N n) → Ω) → ℝ := fun n => sampledRow (X n) (h n) (w n) (Y n) (hbw n) (cap n) (θ n) y r k
  let E := fun n => {ω : Fin (N n) → Ω | totalWeight (rowWeights (w n) (hbw n) ω) ≤ (k:ℝ)}
  have hT (n : ℕ) : Measurable (T n) := measurable_sampledRow (hX n) (hh n) (hw n) (hY n) _ _ _ _ _ _
  have hE (n : ℕ) : MeasurableSet (E n) := by
    exact measurableSet_le (Finset.measurable_sum _ fun j _ =>
      (hw n).comp (measurable_pi_apply j)) measurable_const
  have hTb (n : ℕ) : ∀ᵐ ω ∂Measure.pi (fun _ : Fin (N n) => μ n),
      0 ≤ T n ω ∧ T n ω ≤ 1*(N n:ℝ)^r := by
    have he (j : Fin (N n)) := (measurePreserving_eval (fun _ : Fin (N n) => μ n) j).quasiMeasurePreserving.ae (hpositive n)
    filter_upwards [ae_all_iff.mpr he] with ω hω
    simpa only [one_mul] using (row_polynomial_bounds (X n) (h n) (w n) (Y n) (hbw n)
      (cap n) (θ n) y r k ω (hNpos n) (fun j => (hω j).1) (fun j => (hω j).2) (hcap n) (hθ n)).1
  have hprob := weight_failure_probability μ N hNpos hN w hw hbw k hz hmean
  have hsmall := rare_bad_event_replacement μ N hN T hT E hE r
    (by norm_num : (0:ℝ) ≤ 1) (by norm_num : (0:ℝ) ≤ 1)
    (by positivity : 0 < 2*(z/4)^2) hTb (by simpa only [one_mul] using hprob)
  simpa only [safe_difference] using hsmall

theorem fixed_imbalance_safe_moments (A : CenteredArray Ω)
    [∀ n,Nonempty (Fin (A.N n))] (hgap : A.CompactGap)
    (U h w : ℕ → Ω → ℝ) (r cap θn : ℕ → ℝ)
    (hU : ∀ n,Measurable (U n)) (hh : ∀ n,Measurable (h n))
    (hw : ∀ n,Measurable (w n))
    (hbU : ∀ n x,U n x ∈ Icc (0:ℝ) 1)
    (hbh : ∀ n x,|h n x| ≤ 1) (hbw : ∀ n x,w n x ∈ Icc (0:ℝ) 1)
    (hbal : ∀ n x,w n x ≠ 0 → U n x+h n x=1/2 ∧ A.Y n x=0)
    (hhpos : ∀ n,∀ᵐ x ∂A.law n,0 ≤ h n x)
    (hr : ∀ n,r n ∈ Icc (0:ℝ) 1)
    (hcenter : ∀ n,∀ᵐ x ∂A.law n,A.X n x=U n x-r n)
    (hmatch : ∀ᶠ n in atTop,cap n=(A.N n:ℝ)*r n)
    (hcap : ∀ n,cap n ≤ (A.N n:ℝ))
    (k : ℕ) (y : ℤ) {θ lo hi a z : ℝ} (hlo : 0 < lo)
    (hbracket : ∀ n,lo ≤ θn n ∧ θn n ≤ hi)
    (hθn : Tendsto θn atTop (𝓝 θ)) (hθ : 0 < θ) (hz : 0 < z)
    (hwmean : Tendsto (fun n => ∫ x,w n x ∂A.law n) atTop (𝓝 z))
    (hmean : Tendsto (fun n => ∫ x,w n x*Real.exp (-θn n*h n x) ∂A.law n)
      atTop (𝓝 a)) :
    ∀ q : Fin 3,Tendsto (fun n => (A.N n:ℝ)*∫ ω : Fin (A.N n) → Ω,
      safeRow (U n) (h n) (w n) (A.Y n) (hbw n) (cap n) (θn n) y q.val k ω
        ∂Measure.pi (fun _ : Fin (A.N n) => A.law n)) atTop
      (𝓝 ((a/z)^k*(density A.vX A.vY*(q.val.factorial:ℝ)/θ^(q.val+1)))) := by
  have hraw := fixed_imbalance_sampled_moments A hgap U h w r cap θn hU hh hw hbU hbh hbw
    hbal hhpos hr hcenter hmatch hcap k y hlo hbracket hθn hθ hz hwmean hmean
  have hpositive (n : ℕ) : ∀ᵐ x ∂A.law n,0 ≤ U n x ∧ 0 ≤ h n x :=
    (hhpos n).mono fun x hx => ⟨(hbU n x).1,hx⟩
  intro q
  have hd := fixed_safe_difference A.law A.N (fun n => Nat.cast_pos.mp (A.N_pos n))
    A.market U h w A.Y hU hh hw A.measurable_Y hbw hpositive cap θn hcap
    (fun n => hlo.le.trans (hbracket n).1) y q.val k hz hwmean
  have hi (n : ℕ) := polynomial_sampled_ae (A.law n) (Nat.cast_pos.mp (A.N_pos n))
    (U n) (h n) (w n) (A.Y n) (hbw n) (hpositive n) (hcap n)
    (hlo.le.trans (hbracket n).1) y q.val k
  have hRi (n : ℕ) : Integrable
      (sampledRow (U n) (h n) (w n) (A.Y n) (hbw n) (cap n) (θn n) y q.val k)
      (Measure.pi (fun _ : Fin (A.N n) => A.law n)) :=
    Integrable.of_mem_Icc 0 _
      (measurable_sampledRow (hU n) (hh n) (hw n) (A.measurable_Y n) _ _ _ _ _ _).aemeasurable
      ((hi n).mono fun _ hx => hx.1)
  have hSi (n : ℕ) : Integrable
      (safeRow (U n) (h n) (w n) (A.Y n) (hbw n) (cap n) (θn n) y q.val k)
      (Measure.pi (fun _ : Fin (A.N n) => A.law n)) :=
    Integrable.of_mem_Icc 0 _
      (measurable_safeRow (hU n) (hh n) (hw n) (A.measurable_Y n) _ _ _ _ _ _).aemeasurable
      ((hi n).mono fun _ hx => hx.2)
  have he (n : ℕ) : (A.N n:ℝ)*(∫ ω,
      sampledRow (U n) (h n) (w n) (A.Y n) (hbw n) (cap n) (θn n) y q.val k ω
        ∂Measure.pi (fun _ : Fin (A.N n) => A.law n))-
      (A.N n:ℝ)*(∫ ω,
        sampledRow (U n) (h n) (w n) (A.Y n) (hbw n) (cap n) (θn n) y q.val k ω-
        safeRow (U n) (h n) (w n) (A.Y n) (hbw n) (cap n) (θn n) y q.val k ω
        ∂Measure.pi (fun _ : Fin (A.N n) => A.law n))=
      (A.N n:ℝ)*(∫ ω,
        safeRow (U n) (h n) (w n) (A.Y n) (hbw n) (cap n) (θn n) y q.val k ω
        ∂Measure.pi (fun _ : Fin (A.N n) => A.law n)) := by
    rw [integral_sub (hRi n) (hSi n)]
    ring
  have hsmall := (hraw q).sub hd
  simp only [he,sub_zero] at hsmall
  convert! hsmall using 1
  rw [div_pow]
  ring

end FCAppendix.Affine.Uniform06.SampledSafeLimit
