import FCAppendix.Probability.BernoulliPairs
import FCAppendix.Probability.WeakMomentConvergence

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.EntryVector
open MeasureTheory ProbabilityTheory Matrix Set Filter Topology
open scoped BigOperators

local instance : Convexity.ConvexSpace ℝ (EuclideanSpace ℝ (Fin 2)) :=
  Convexity.ConvexSpace.ofModule
local instance : Convexity.IsModuleConvexSpace ℝ (EuclideanSpace ℝ (Fin 2)) :=
  Convexity.IsModuleConvexSpace.ofModule

universe u
variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {N : ℕ}

def pair (A : Fin N → Fin 2 → Ω → ℝ) (i : Fin N) (ω : Ω) :
    EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 (fun j => A i j ω)

def scale (N : ℕ) (v : Fin 2 → ℝ) (j : Fin 2) : ℝ :=
  Real.sqrt (N : ℝ)*Real.sqrt (v j)

def standardized (A : Fin N → Fin 2 → Ω → ℝ) (v : Fin 2 → ℝ)
    (i : Fin N) (ω : Ω) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 (fun j => A i j ω/scale N v j)

lemma scale_pos (hN : 0 < N) {v : Fin 2 → ℝ} (hv : ∀ j, 0 < v j) (j : Fin 2) :
    0 < scale N v j :=
  mul_pos (Real.sqrt_pos.mpr (by exact_mod_cast hN)) (Real.sqrt_pos.mpr (hv j))

lemma scale_sq (v : Fin 2 → ℝ) (hv : ∀ j, 0 ≤ v j) (j : Fin 2) :
    (scale N v j)^2=(N : ℝ)*v j := by
  rw [scale,mul_pow,Real.sq_sqrt (Nat.cast_nonneg _),Real.sq_sqrt (hv j)]

lemma measurable_standardized (A : Fin N → Fin 2 → Ω → ℝ) (v : Fin 2 → ℝ)
    (hm : ∀ i j, Measurable (A i j)) (i : Fin N) :
    Measurable (standardized A v i) := by
  unfold standardized
  fun_prop

lemma memLp_coordinate (A : Fin N → Fin 2 → Ω → ℝ)
    (hm : ∀ i j, Measurable (A i j))
    (hb : ∀ i j, ∀ᵐ ω ∂μ, |A i j ω| ≤ 1) (q : ENNReal) (i : Fin N) (j : Fin 2) :
    MemLp (A i j) q μ :=
  MemLp.of_bound (hm i j).aestronglyMeasurable 1 (by simpa only [Real.norm_eq_abs] using hb i j)

lemma memLp_standardized_coordinate (A : Fin N → Fin 2 → Ω → ℝ) (v : Fin 2 → ℝ)
    (hm : ∀ i j, Measurable (A i j))
    (hb : ∀ i j, ∀ᵐ ω ∂μ, |A i j ω| ≤ 1) (q : ENNReal) (i : Fin N) (j : Fin 2) :
    MemLp (fun ω => standardized A v i ω j) q μ := by
  simpa only [standardized,WithLp.ofLp_toLp,div_eq_mul_inv] using
    (memLp_coordinate A hm hb q i j).mul_const (scale N v j)⁻¹

lemma memLp_standardized (A : Fin N → Fin 2 → Ω → ℝ) (v : Fin 2 → ℝ)
    (hm : ∀ i j, Measurable (A i j))
    (hb : ∀ i j, ∀ᵐ ω ∂μ, |A i j ω| ≤ 1) (q : ENNReal) (i : Fin N) :
    MemLp (standardized A v i) q μ :=
  MemLp.of_eval_piLp (memLp_standardized_coordinate A v hm hb q i)

lemma integral_standardized (A : Fin N → Fin 2 → Ω → ℝ) (v : Fin 2 → ℝ)
    (hm : ∀ i j, Measurable (A i j))
    (hb : ∀ i j, ∀ᵐ ω ∂μ, |A i j ω| ≤ 1)
    (hzero : ∀ i j, ∫ ω, A i j ω ∂μ=0) (i : Fin N) :
    (∫ ω, standardized A v i ω ∂μ)=0 := by
  ext j
  rw [eval_integral_piLp (fun j =>
    (memLp_standardized_coordinate A v hm hb 1 i j).integrable le_rfl)]
  simp only [standardized,WithLp.ofLp_toLp,integral_div,hzero,zero_div,PiLp.zero_apply]

omit [IsProbabilityMeasure μ] in
lemma indep_standardized (A : Fin N → Fin 2 → Ω → ℝ) (v : Fin 2 → ℝ)
    (hi : iIndepFun (pair A) μ) : iIndepFun (standardized A v) μ := by
  have hh := hi.comp
    (fun (_ : Fin N) (x : EuclideanSpace ℝ (Fin 2)) =>
      WithLp.toLp 2 (fun j => x j/scale N v j)) (fun _ => by fun_prop)
  convert! hh using 1

omit [IsProbabilityMeasure μ] in
lemma covariance_standardized_coordinate (A : Fin N → Fin 2 → Ω → ℝ)
    (v : Fin 2 → ℝ) (hN : 0 < N) (hv : ∀ j, 0 < v j)
    (hcov : ∀ i j k, covariance (A i j) (A i k) μ = if j=k then v j else 0)
    (i : Fin N) (j k : Fin 2) :
    covariance (fun ω => standardized A v i ω j)
      (fun ω => standardized A v i ω k) μ = if j=k then 1/(N : ℝ) else 0 := by
  simp only [standardized,WithLp.ofLp_toLp]
  rw [covariance_fun_div_left,covariance_fun_div_right,hcov]
  by_cases he : j=k
  · subst k
    rw [if_pos rfl,if_pos rfl,div_div,← pow_two,scale_sq v (fun j => (hv j).le)]
    field_simp [(hv j).ne',(show (N : ℝ) ≠ 0 by exact_mod_cast hN.ne')]
  · simp [he]

theorem covarianceBilin_standardized_sum (A : Fin N → Fin 2 → Ω → ℝ)
    (v : Fin 2 → ℝ) (hN : 0 < N) (hv : ∀ j, 0 < v j)
    (hm : ∀ i j, Measurable (A i j))
    (hb : ∀ i j, ∀ᵐ ω ∂μ, |A i j ω| ≤ 1)
    (hi : iIndepFun (pair A) μ)
    (hcov : ∀ i j k, covariance (A i j) (A i k) μ = if j=k then v j else 0)
    (x y : EuclideanSpace ℝ (Fin 2)) :
    covarianceBilin (μ.map (fun ω => ∑ i, standardized A v i ω)) x y =
      x ⬝ᵥ (1 : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ y := by
  rw [covarianceBilin_map_sum_eq_sum (memLp_standardized A v hm hb 2)
    (indep_standardized A v hi)]
  have he (i : Fin N) :
      covarianceBilin (μ.map (standardized A v i)) x y =
      (x 0*y 0+x 1*y 1)/(N : ℝ) := by
    rw [covarianceBilin_apply_pi (memLp_standardized_coordinate A v hm hb 2 i) x y]
    simp only [Fin.sum_univ_two,covariance_standardized_coordinate A v hN hv hcov,
      if_true,if_false,Fin.zero_ne_one,(show (1 : Fin 2) ≠ 0 by decide),mul_zero,add_zero]
    ring
  simp_rw [he]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
    one_mulVec,dotProduct,Fin.sum_univ_two]
  field_simp [(show (N : ℝ) ≠ 0 by exact_mod_cast hN.ne')]

omit [IsProbabilityMeasure μ] in
lemma norm_standardized_le (A : Fin N → Fin 2 → Ω → ℝ) (v : Fin 2 → ℝ)
    (hN : 0 < N) {η : ℝ} (hη : 0 < η) (hv : ∀ j, η ≤ v j)
    (hb : ∀ i j, ∀ᵐ ω ∂μ, |A i j ω| ≤ 1) (i : Fin N) :
    ∀ᵐ ω ∂μ, ‖standardized A v i ω‖ ≤ 2/(Real.sqrt (N : ℝ)*Real.sqrt η) := by
  let d := Real.sqrt (N : ℝ)*Real.sqrt η
  have hd : 0 < d := mul_pos (Real.sqrt_pos.mpr (by exact_mod_cast hN)) (Real.sqrt_pos.mpr hη)
  have hvp (j : Fin 2) : 0 < v j := hη.trans_le (hv j)
  have hdl (j : Fin 2) : d ≤ scale N v j :=
    mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hv j)) (Real.sqrt_nonneg _)
  filter_upwards [ae_all_iff.mpr (hb i)] with ω hω
  have hc (j : Fin 2) : |standardized A v i ω j| ≤ 1/d := by
    change |A i j ω/scale N v j| ≤ _
    rw [abs_div,abs_of_pos (scale_pos hN hvp j)]
    exact (div_le_div_of_nonneg_right (hω j) (scale_pos hN hvp j).le).trans
      (one_div_le_one_div_of_le hd (hdl j))
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ 2/d)).mp
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [Fin.sum_univ_two]
  have h0 := (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ 1/d)).mpr (hc 0)
  have h1 := (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ 1/d)).mpr (hc 1)
  rw [sq_abs] at h0 h1
  have hpow : (2/d)^2=4*(1/d)^2 := by ring
  rw [hpow]
  nlinarith [sq_nonneg (1/d)]

def fold (a b : ℝ) (x : EuclideanSpace ℝ (Fin 2)) : ℝ := a*x 0+b*|x 1|
def foldedSublevel (a b s : ℝ) : Set (EuclideanSpace ℝ (Fin 2)) := {x | fold a b x ≤ s}

lemma continuous_fold (a b : ℝ) : Continuous (fold a b) := by unfold fold; fun_prop
lemma measurableSet_foldedSublevel (a b s : ℝ) : MeasurableSet (foldedSublevel a b s) :=
  measurableSet_le (continuous_fold a b).measurable measurable_const

lemma convex_foldedSublevel (a : ℝ) {b : ℝ} (hb : 0 ≤ b) (s : ℝ) :
    Convexity.IsConvexSet ℝ (foldedSublevel a b s) := by
  apply Convexity.IsConvexSet.of_convexCombPair_mem
  intro r t hr ht hrt x hx y hy
  rw [Convexity.convexCombPair_eq_sum]
  change a*(r*x 0+t*y 0)+b*|r*x 1+t*y 1| ≤ s
  have habs : |r*x 1+t*y 1| ≤ r*|x 1|+t*|y 1| := by
    simpa only [abs_mul,abs_of_nonneg hr,abs_of_nonneg ht] using abs_add_le (r*x 1) (t*y 1)
  have h1 := mul_le_mul_of_nonneg_left hx hr
  have h2 := mul_le_mul_of_nonneg_left hy ht
  have h3 := mul_le_mul_of_nonneg_left habs hb
  change r*(a*x 0+b*|x 1|) ≤ r*s at h1
  change t*(a*y 0+b*|y 1|) ≤ t*s at h2
  nlinarith [congrArg (fun z : ℝ => z*s) hrt]

theorem exists_standardized_folded_cdf_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω]
      (μ : Measure Ω) [IsProbabilityMeasure μ]
      (N : ℕ) (A : Fin N → Fin 2 → Ω → ℝ) (v : Fin 2 → ℝ)
      (η : ℝ), 0 < N → 0 < η → (∀ j, η ≤ v j) →
      (∀ i j, Measurable (A i j)) →
      (∀ i j, ∀ᵐ ω ∂μ, |A i j ω| ≤ 1) →
      (∀ i j, ∫ ω, A i j ω ∂μ=0) →
      iIndepFun (pair A) μ →
      (∀ i j k, covariance (A i j) (A i k) μ = if j=k then v j else 0) →
      ∀ a b s, 0 ≤ b →
      |μ.real {ω | fold a b (∑ i, standardized A v i ω) ≤ s} -
        (stdGaussian (EuclideanSpace ℝ (Fin 2))).real (foldedSublevel a b s)| ≤
        C/((Real.sqrt η)^3*Real.sqrt (N : ℝ)) := by
  obtain ⟨C,hC,hBE⟩ := FCAppendix.BoundedVectorApproximation.exists_bounded_convex_bound.{u}
  refine ⟨8*C*(2 : ℝ)^(1/4 : ℝ),by positivity,?_⟩
  intro Ω _ μ _ N A v η hN hη hv hm hb hz hi hcov a b s hb0
  have hvp (j : Fin 2) : 0 < v j := hη.trans_le (hv j)
  have hcorr : FCAppendix.CorrelationMatrix.corr 0 = (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [FCAppendix.CorrelationMatrix.corr]
  have hI : (1 : Matrix (Fin 2) (Fin 2) ℝ).PosDef := by
    rw [← hcorr]
    exact FCAppendix.CorrelationMatrix.corr_posDef (r := 0) (by norm_num)
  have hw : ‖bentkusWhiteningCLM (1 : Matrix (Fin 2) (Fin 2) ℝ)‖ ≤ 1 := by
    rw [← hcorr]
    simpa using FCAppendix.CorrelationMatrix.corr_whitening_norm_le (r := 0) (by norm_num)
  have hB := hBE (by norm_num : 0 < 2) μ (standardized A v)
    (1 : Matrix (Fin 2) (Fin 2) ℝ) (2/(Real.sqrt (N : ℝ)*Real.sqrt η))
    (measurable_standardized A v hm) (norm_standardized_le A v hN hη hv hb)
    (indep_standardized A v hi) (integral_standardized A v hm hb hz)
    hI (covarianceBilin_standardized_sum A v hN hvp hm hb hi hcov)
    (foldedSublevel a b s) (measurableSet_foldedSublevel a b s) (convex_foldedSublevel a hb0 s)
  have hsum : Measurable (fun ω => ∑ i, standardized A v i ω) := by
    exact Finset.measurable_sum _ (fun i _ => measurable_standardized A v hm i)
  simp only [Measure.real] at hB
  rw [Measure.map_apply hsum (measurableSet_foldedSublevel a b s)] at hB
  simp only [multivariateGaussian_zero_one] at hB
  have hroot : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hN)
  have hηroot : 0 < Real.sqrt η := Real.sqrt_pos.mpr hη
  have hfactor :
      C*(2 : ℝ)^(1/4 : ℝ)*(N : ℝ)*
        (‖bentkusWhiteningCLM (1 : Matrix (Fin 2) (Fin 2) ℝ)‖ *
          (2/(Real.sqrt (N : ℝ)*Real.sqrt η)))^3 ≤
      C*(2 : ℝ)^(1/4 : ℝ)*(N : ℝ)*(2/(Real.sqrt (N : ℝ)*Real.sqrt η))^3 := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact pow_le_pow_left₀ (by positivity)
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hw (by positivity)) 3
  have halgebra :
      C*(2 : ℝ)^(1/4 : ℝ)*(N : ℝ)*(2/(Real.sqrt (N : ℝ)*Real.sqrt η))^3 =
      (8*C*(2 : ℝ)^(1/4 : ℝ))/((Real.sqrt η)^3*Real.sqrt (N : ℝ)) := by
    have hs := Real.sq_sqrt (Nat.cast_nonneg N)
    field_simp [hroot.ne',hηroot.ne']
    nlinarith [congrArg (fun z : ℝ => 8*C*(2 : ℝ)^(1/4 : ℝ)*z) hs]
  exact hB.trans (hfactor.trans_eq halgebra)

end FCAppendix.Affine.Uniform06.EntryVector
