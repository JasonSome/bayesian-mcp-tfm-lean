import FCAppendix.Affine.Uniform06.EntryGaussianLaw
import FCAppendix.Probability.CDFWeakConvergence
import FCAppendix.Probability.UniformMovingThreshold

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.EntryCentral
open MeasureTheory ProbabilityTheory Matrix Set Filter Topology
open FCAppendix.Affine.Uniform06.EntryVector
open scoped BigOperators

universe u
variable {Ω : ℕ → Type u} [∀ m, MeasurableSpace (Ω m)]
  (μ : (m : ℕ) → Measure (Ω m)) [∀ m, IsProbabilityMeasure (μ m)]
  (N : ℕ → ℕ) (A : (m : ℕ) → Fin (N m) → Fin 2 → Ω m → ℝ)
  (v : ℕ → Fin 2 → ℝ)

def foldedRow (a b : ℕ → ℝ) (m : ℕ) (ω : Ω m) : ℝ :=
  fold (a m) (b m) (∑ i, standardized (A m) (v m) i ω)

lemma measurable_foldedRow (a b : ℕ → ℝ)
    (hm : ∀ m i j, Measurable (A m i j)) (m : ℕ) :
    Measurable (foldedRow N A v a b m) :=
  (continuous_fold (a m) (b m)).measurable.comp
    (Finset.measurable_sum _ (fun i _ => measurable_standardized (A m) (v m) (hm m) i))

theorem constructed_folded_cdf_tendsto
    (hN : Tendsto N atTop atTop)
    (hm : ∀ m i j, Measurable (A m i j))
    (hb : ∀ m i j, ∀ᵐ ω ∂μ m, |A m i j ω| ≤ 1)
    (hz : ∀ m i j, ∫ ω, A m i j ω ∂μ m=0)
    (hi : ∀ m, iIndepFun (pair (A m)) (μ m))
    (hcov : ∀ m i j k, covariance (A m i j) (A m i k) (μ m) =
      if j=k then v m j else 0)
    {η : ℝ} (hη : 0 < η) (hv : ∀ᶠ m in atTop, ∀ j, η ≤ v m j)
    (a b s : ℕ → ℝ) {a0 b0 s0 : ℝ}
    (ha : ∀ m, 0 < a m) (ha0 : 0 < a0) (hbb : ∀ᶠ m in atTop, 0 ≤ b m)
    (haL : Tendsto a atTop (𝓝 a0)) (hbL : Tendsto b atTop (𝓝 b0))
    (hsL : Tendsto s atTop (𝓝 s0)) :
    Tendsto (fun m => (μ m).real {ω | foldedRow N A v a b m ω ≤ s m})
      atTop (𝓝 (cdf (EntryGaussianLaw.law a0 b0) s0)) := by
  obtain ⟨C,hC,hBE⟩ := exists_standardized_folded_cdf_bound.{u}
  have hroot : Tendsto (fun m => Real.sqrt (N m : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp hN)
  have herr : Tendsto (fun m => C/((Real.sqrt η)^3*Real.sqrt (N m : ℝ)))
      atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (hroot.const_mul_atTop (by positivity))
  have hG := EntryGaussianLaw.cdf_moving_tendsto a b s ha0 ha haL hbL hsL
  have he : Tendsto (fun m => (μ m).real {ω | foldedRow N A v a b m ω ≤ s m} -
      cdf (EntryGaussianLaw.law (a m) (b m)) (s m)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ herr
    filter_upwards [hv,hbb,hN.eventually_gt_atTop 0] with m hvm hbm hNm
    rw [Real.norm_eq_abs,EntryGaussianLaw.cdf_eq_standardGaussian_sublevel]
    exact hBE (μ m) (N m) (A m) (v m) η hNm hη hvm (hm m) (hb m)
      (hz m) (hi m) (hcov m) (a m) (b m) (s m) hbm
  simpa only [sub_add_cancel,zero_add] using he.add hG

theorem constructed_folded_weak_limit
    (hN : Tendsto N atTop atTop)
    (hm : ∀ m i j, Measurable (A m i j))
    (hb : ∀ m i j, ∀ᵐ ω ∂μ m, |A m i j ω| ≤ 1)
    (hz : ∀ m i j, ∫ ω, A m i j ω ∂μ m=0)
    (hi : ∀ m, iIndepFun (pair (A m)) (μ m))
    (hcov : ∀ m i j k, covariance (A m i j) (A m i k) (μ m) =
      if j=k then v m j else 0)
    {η : ℝ} (hη : 0 < η) (hv : ∀ᶠ m in atTop, ∀ j, η ≤ v m j)
    (a b : ℕ → ℝ) {a0 b0 : ℝ}
    (ha : ∀ m, 0 < a m) (ha0 : 0 < a0) (hbb : ∀ᶠ m in atTop, 0 ≤ b m)
    (haL : Tendsto a atTop (𝓝 a0)) (hbL : Tendsto b atTop (𝓝 b0)) :
    TendstoInDistribution (foldedRow N A v a b) atTop
      (EntryGaussianLaw.sumFold a0 b0) μ
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
  have hmrow := measurable_foldedRow N A v a b hm
  refine ⟨fun m => (hmrow m).aemeasurable,
    (EntryGaussianLaw.continuous_sumFold a0 b0).measurable.aemeasurable,?_⟩
  apply FCAppendix.Probability.probabilityMeasure_tendsto_of_cdf
  intro s
  have h := constructed_folded_cdf_tendsto μ N A v hN hm hb hz hi hcov hη hv
    a b (fun _ => s) ha ha0 hbb haL hbL tendsto_const_nhds
  convert! h using 1
  funext m
  haveI := Measure.isProbabilityMeasure_map (μ := μ m) (hmrow m).aemeasurable
  rw [cdf_eq_real]
  change (Measure.map (foldedRow N A v a b m) (μ m)).real (Iic s) = _
  rw [map_measureReal_apply (hmrow m) measurableSet_Iic]
  rfl

theorem eventually_positive_central_success
    (hN : Tendsto N atTop atTop)
    (hm : ∀ m i j, Measurable (A m i j))
    (hb : ∀ m i j, ∀ᵐ ω ∂μ m, |A m i j ω| ≤ 1)
    (hz : ∀ m i j, ∫ ω, A m i j ω ∂μ m=0)
    (hi : ∀ m, iIndepFun (pair (A m)) (μ m))
    (hcov : ∀ m i j k, covariance (A m i j) (A m i k) (μ m) =
      if j=k then v m j else 0)
    {η : ℝ} (hη : 0 < η) (hv : ∀ᶠ m in atTop, ∀ j, η ≤ v m j)
    (a b z : ℕ → ℝ) {a0 b0 z0 : ℝ}
    (ha : ∀ m, 0 < a m) (ha0 : 0 < a0) (hbb : ∀ᶠ m in atTop, 0 ≤ b m)
    (haL : Tendsto a atTop (𝓝 a0)) (hbL : Tendsto b atTop (𝓝 b0))
    (hzL : Tendsto z atTop (𝓝 z0)) :
    ∃ q : ℝ, 0 < q ∧ ∀ᶠ m in atTop,
      q ≤ (μ m).real {ω | foldedRow N A v a b m ω < z m} := by
  let p := cdf (EntryGaussianLaw.law a0 b0) (z0-1)
  have hp : 0 < p := EntryGaussianLaw.cdf_pos ha0 b0 (z0-1)
  have hlim := constructed_folded_cdf_tendsto μ N A v hN hm hb hz hi hcov hη hv
    a b (fun _ => z0-1) ha ha0 hbb haL hbL tendsto_const_nhds
  refine ⟨p/2,by positivity,?_⟩
  filter_upwards [hlim.eventually (Ioi_mem_nhds (show p/2 < p by linarith)),
    hzL.eventually (Ioi_mem_nhds (show z0-1 < z0 by linarith))] with m hm hzm
  apply hm.le.trans
  exact measureReal_mono (fun ω hω => hω.trans_lt hzm)

section FinitePerturbations
variable {Ω' : Type*} [MeasurableSpace Ω'] (P : Measure Ω') [IsProbabilityMeasure P]

theorem cdf_lower_of_L2 (F T : Ω' → ℝ) (s ε : ℝ) (hε : 0 < ε)
    (hint : Integrable (fun ω => (F ω-T ω)^2) P) :
    P.real {ω | F ω ≤ s-ε}-(∫ ω, (F ω-T ω)^2 ∂P)/ε^2 ≤
      P.real {ω | T ω ≤ s} := by
  have hcover : {ω | F ω ≤ s-ε} ⊆
      {ω | T ω ≤ s} ∪ {ω | ε^2 ≤ (F ω-T ω)^2} := by
    intro ω hω
    by_cases hT : T ω ≤ s
    · exact Or.inl hT
    · right
      change ε^2 ≤ (F ω-T ω)^2
      have hF : F ω ≤ s-ε := hω
      have hd : ε < T ω-F ω := by linarith
      have hs := (sq_lt_sq₀ hε.le (by linarith : 0 ≤ T ω-F ω)).mpr hd
      nlinarith
  have hprob := (measureReal_mono (μ := P) hcover).trans (measureReal_union_le _ _)
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (Eventually.of_forall fun ω => sq_nonneg (F ω-T ω)) hint (ε^2)
  have hsmall : P.real {ω | ε^2 ≤ (F ω-T ω)^2} ≤
      (∫ ω, (F ω-T ω)^2 ∂P)/ε^2 :=
    (le_div_iff₀ (sq_pos_of_pos hε)).mpr (by nlinarith [hmarkov])
  linarith

theorem cdf_upper_of_L2 (F T : Ω' → ℝ) (s ε : ℝ) (hε : 0 < ε)
    (hint : Integrable (fun ω => (F ω-T ω)^2) P) :
    P.real {ω | T ω ≤ s} ≤ P.real {ω | F ω ≤ s+ε}+
      (∫ ω, (F ω-T ω)^2 ∂P)/ε^2 := by
  have hswap : (fun ω => (T ω-F ω)^2)=(fun ω => (F ω-T ω)^2) :=
    funext fun _ => by ring
  have hh := cdf_lower_of_L2 P T F (s+ε) ε hε (hswap ▸ hint)
  rw [hswap] at hh
  simp only [add_sub_cancel_right] at hh
  linarith

end FinitePerturbations
end FCAppendix.Affine.Uniform06.EntryCentral
