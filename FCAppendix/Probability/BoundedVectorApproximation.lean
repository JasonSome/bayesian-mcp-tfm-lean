import ProbabilityApproximation.Bentkus.Induction
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.MeasureTheory.Measure.Portmanteau

noncomputable section

namespace FCAppendix.BoundedVectorApproximation

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped BigOperators

universe u

local instance moduleConvexSpace {d : ℕ} : Convexity.ConvexSpace ℝ (EuclideanSpace ℝ (Fin d)) :=
  Convexity.ConvexSpace.ofModule

local instance moduleConvexSpaceCompatible {d : ℕ} :
    Convexity.IsModuleConvexSpace ℝ (EuclideanSpace ℝ (Fin d)) :=
  Convexity.IsModuleConvexSpace.ofModule

def lowerOrthant {d : ℕ} (a : Fin d → ℝ) : Set (EuclideanSpace ℝ (Fin d)) :=
  {x | ∀ i, x i ≤ a i}

lemma measurableSet_lowerOrthant {d : ℕ} (a : Fin d → ℝ) : MeasurableSet (lowerOrthant a) := by
  simp only [lowerOrthant, Set.setOf_forall]
  exact MeasurableSet.iInter fun i => measurableSet_le (by fun_prop) measurable_const

lemma convex_lowerOrthant {d : ℕ} (a : Fin d → ℝ) :
    Convexity.IsConvexSet ℝ (lowerOrthant a) := by
  apply Convexity.IsConvexSet.of_convexCombPair_mem
  intro r s hr hs hrs x hx y hy i
  rw [Convexity.convexCombPair_eq_sum]
  change r * x i + s * y i ≤ a i
  have h1 := mul_le_mul_of_nonneg_left (hx i) hr
  have h2 := mul_le_mul_of_nonneg_left (hy i) hs
  calc
    _ ≤ r * a i + s * a i := add_le_add h1 h2
    _ = _ := by rw [← add_mul, hrs, one_mul]

theorem gaussian_isOpenPosMeasure {d : ℕ} (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosDef) :
    (multivariateGaussian 0 S).IsOpenPosMeasure := by
  haveI : (gaussianReal 0 1).IsOpenPosMeasure :=
    (gaussianReal_absolutelyContinuous' (0 : ℝ) (by norm_num : (1 : NNReal) ≠ 0)).isOpenPosMeasure
  haveI : (stdGaussian (EuclideanSpace ℝ (Fin d))).IsOpenPosMeasure := by
    rw [← map_pi_eq_stdGaussian]
    exact (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ)).isOpenPosMeasure_map (WithLp.toLp_surjective 2)
  let e := (bentkusWhiteningEquiv S hS).symm
  have hmap : (stdGaussian (EuclideanSpace ℝ (Fin d))).map e = multivariateGaussian 0 S := by
    unfold multivariateGaussian
    congr 1
    funext x
    simp only [e, bentkusWhiteningEquiv_symm_apply, zero_add]
  rw [← hmap]
  exact e.continuous.isOpenPosMeasure_map e.surjective

theorem gaussian_lowerOrthant_pos {d : ℕ} (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosDef)
    (a : Fin d → ℝ) : 0 < (multivariateGaussian 0 S).real (lowerOrthant a) := by
  haveI := gaussian_isOpenPosMeasure S hS
  have hopen : IsOpen {x : EuclideanSpace ℝ (Fin d) | ∀ i, x i < a i} := by
    simp only [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun i => isOpen_lt (by fun_prop) continuous_const
  have hne : {x : EuclideanSpace ℝ (Fin d) | ∀ i, x i < a i}.Nonempty :=
    ⟨WithLp.toLp 2 (fun i => a i - 1), fun i => by simp⟩
  have hp := hopen.measure_pos (multivariateGaussian 0 S) hne
  have hsub : {x : EuclideanSpace ℝ (Fin d) | ∀ i, x i < a i} ⊆ lowerOrthant a :=
    fun _ hx i => (hx i).le
  exact ENNReal.toReal_pos (ne_of_gt (hp.trans_le (measure_mono hsub))) (measure_ne_top _ _)

lemma thirdMoment_comp_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {d : ℕ}
    (T : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (X : Ω → EuclideanSpace ℝ (Fin d)) (hX : MemLp X 3 μ)
    (B : ℝ) (hB : ∀ᵐ ω ∂μ, ‖X ω‖ ≤ B) :
    (∫ ω, ‖T (X ω)‖ ^ 3 ∂μ) ≤ (‖T‖ * B) ^ 3 := by
  have hW : MemLp (fun ω => T (X ω)) 3 μ := by
    simpa only [Function.comp_def] using hX.continuousLinearMap_comp T
  calc
    _ ≤ ∫ _ω : Ω, (‖T‖ * B) ^ 3 ∂μ := by
      apply integral_mono_ae (hW.integrable_norm_pow (by decide : (3 : ℕ) ≠ 0))
        (integrable_const _)
      filter_upwards [hB] with ω hω
      exact pow_le_pow_left₀ (norm_nonneg _) ((ContinuousLinearMap.le_opNorm T _).trans
        (mul_le_mul_of_nonneg_left hω (norm_nonneg T))) _
    _ = _ := by simp

theorem exists_bounded_convex_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ {d n : ℕ} (_hd : 0 < d) {Ω : Type u} [MeasurableSpace Ω]
        (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : Fin n → Ω → EuclideanSpace ℝ (Fin d))
        (S : Matrix (Fin d) (Fin d) ℝ) (B : ℝ),
        (∀ i, Measurable (X i)) → (∀ i, ∀ᵐ ω ∂μ, ‖X i ω‖ ≤ B) →
        iIndepFun X μ → (∀ i, ∫ ω, X i ω ∂μ = 0) → S.PosDef →
        (∀ x y, covarianceBilin (μ.map (fun ω ↦ ∑ i, X i ω)) x y = x ⬝ᵥ S *ᵥ y) →
        ∀ A : Set (EuclideanSpace ℝ (Fin d)), MeasurableSet A → Convexity.IsConvexSet ℝ A →
          |(μ.map (fun ω ↦ ∑ i, X i ω)).real A - (multivariateGaussian 0 S).real A| ≤
            C * (d : ℝ) ^ (1 / 4 : ℝ) * n * (‖bentkusWhiteningCLM S‖ * B) ^ 3 := by
  obtain ⟨C, hC, hBE⟩ := exists_bentkus_convex_set_constant.{u}
  refine ⟨C, hC, ?_⟩
  intro d n hd Ω _ μ _ X S B hXm hXB hXi hX0 hS hcov A hAm hAc
  have hX3 : ∀ i, MemLp (X i) 3 μ := fun i =>
    MemLp.of_bound (hXm i).aestronglyMeasurable B (hXB i)
  have hbound : (∑ i, ∫ ω, ‖bentkusWhiteningCLM S (X i ω)‖ ^ 3 ∂μ) ≤
      n * (‖bentkusWhiteningCLM S‖ * B) ^ 3 := by
    calc
      _ ≤ ∑ _i : Fin n, (‖bentkusWhiteningCLM S‖ * B) ^ 3 := by
        exact Finset.sum_le_sum fun i _ =>
          thirdMoment_comp_le μ (bentkusWhiteningCLM S) (X i) (hX3 i) B (hXB i)
      _ = _ := by simp
  have hb := hBE hd μ X S hX3 hXi hX0 hS hcov A hAm hAc
  change _ ≤ C * (d : ℝ) ^ (1 / 4 : ℝ) *
    (∑ i, ∫ ω, ‖bentkusWhiteningCLM S (X i ω)‖ ^ 3 ∂μ) at hb
  calc
    _ ≤ C * (d : ℝ) ^ (1 / 4 : ℝ) *
        (n * (‖bentkusWhiteningCLM S‖ * B) ^ 3) :=
      hb.trans (mul_le_mul_of_nonneg_left hbound (mul_nonneg hC.le (by positivity)))
    _ = _ := by ring

def gaussianProbability {d : ℕ} (S : Matrix (Fin d) (Fin d) ℝ) :
    ProbabilityMeasure (EuclideanSpace ℝ (Fin d)) := ⟨multivariateGaussian 0 S, inferInstance⟩

theorem gaussianProbability_tendsto {d : ℕ} (S : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (S₀ : Matrix (Fin d) (Fin d) ℝ) (hS : ∀ n, (S n).PosSemidef) (hS₀ : S₀.PosSemidef)
    (hlim : Tendsto S atTop (𝓝 S₀)) :
    Tendsto (fun n => gaussianProbability (S n)) atTop (𝓝 (gaussianProbability S₀)) := by
  apply ProbabilityMeasure.tendsto_of_tendsto_charFun
  intro x
  change Tendsto (fun n => charFun (multivariateGaussian 0 (S n)) x) atTop
    (𝓝 (charFun (multivariateGaussian 0 S₀) x))
  simp only [charFun_multivariateGaussian (hS _), charFun_multivariateGaussian hS₀]
  have hcont : Continuous (fun A : Matrix (Fin d) (Fin d) ℝ =>
      Complex.exp ((inner ℝ x (0 : EuclideanSpace ℝ (Fin d)) : ℂ) * Complex.I -
        (x ⬝ᵥ A *ᵥ x : ℝ) / 2)) := by fun_prop
  exact (hcont.tendsto S₀).comp hlim

theorem eventually_gaussian_lowerOrthant_pos {d : ℕ}
    (S : ℕ → Matrix (Fin d) (Fin d) ℝ) (S₀ : Matrix (Fin d) (Fin d) ℝ)
    (hS : ∀ n, (S n).PosSemidef) (hS₀ : S₀.PosDef) (hlim : Tendsto S atTop (𝓝 S₀))
    (a : Fin d → ℝ) :
    ∃ q : ℝ, 0 < q ∧ ∀ᶠ n in atTop, q ≤ (multivariateGaussian 0 (S n)).real (lowerOrthant a) := by
  let G : Set (EuclideanSpace ℝ (Fin d)) := {x | ∀ i, x i < a i}
  have hopen : IsOpen G := by
    simp only [G, Set.setOf_forall]
    exact isOpen_iInter_of_finite fun i => isOpen_lt (by fun_prop) continuous_const
  have hne : G.Nonempty := ⟨WithLp.toLp 2 (fun i => a i - 1), fun i => by simp⟩
  haveI := gaussian_isOpenPosMeasure S₀ hS₀
  have hpos := hopen.measure_pos (multivariateGaussian 0 S₀) hne
  have hweak := gaussianProbability_tendsto S S₀ hS hS₀.posSemidef hlim
  have hport := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hweak hopen
  change multivariateGaussian 0 S₀ G ≤
    atTop.liminf (fun n => multivariateGaussian 0 (S n) G) at hport
  obtain ⟨r, hr0, hr⟩ := exists_between hpos
  have hrfin : r ≠ ⊤ := ne_top_of_lt hr
  have he := eventually_lt_of_lt_liminf (hr.trans_le hport)
  refine ⟨r.toReal, ENNReal.toReal_pos hr0.ne' hrfin, ?_⟩
  filter_upwards [he] with n hn
  have hsub : G ⊆ lowerOrthant a := fun _ hx i => (hx i).le
  exact (ENNReal.toReal_mono (measure_ne_top _ _) hn.le).trans (measureReal_mono hsub)

theorem eventually_lowerOrthant_pos_of_small_bound {d : ℕ} (hd : 0 < d)
    {Ω : ℕ → Type u} [∀ n, MeasurableSpace (Ω n)]
    (μ : (n : ℕ) → Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (N : ℕ → ℕ) (X : (n : ℕ) → Fin (N n) → Ω n → EuclideanSpace ℝ (Fin d))
    (S : ℕ → Matrix (Fin d) (Fin d) ℝ) (S₀ : Matrix (Fin d) (Fin d) ℝ) (B : ℕ → ℝ)
    (hXm : ∀ n i, Measurable (X n i))
    (hXB : ∀ n i, ∀ᵐ ω ∂μ n, ‖X n i ω‖ ≤ B n)
    (hXi : ∀ n, iIndepFun (X n) (μ n)) (hX0 : ∀ n i, ∫ ω, X n i ω ∂μ n = 0)
    (hS : ∀ n, (S n).PosDef) (hS₀ : S₀.PosDef)
    (hcov : ∀ n x y, covarianceBilin ((μ n).map (fun ω ↦ ∑ i, X n i ω)) x y =
      x ⬝ᵥ S n *ᵥ y)
    (hlim : Tendsto S atTop (𝓝 S₀))
    (herr : Tendsto (fun n => (N n : ℝ) * (‖bentkusWhiteningCLM (S n)‖ * B n) ^ 3)
      atTop (𝓝 0))
    (a : Fin d → ℝ) (t : ℕ → Fin d → ℝ) (ht : ∀ᶠ n in atTop, ∀ i, a i ≤ t n i) :
    ∃ q : ℝ, 0 < q ∧ ∀ᶠ n in atTop,
      q ≤ ((μ n).map (fun ω ↦ ∑ i, X n i ω)).real (lowerOrthant (t n)) := by
  obtain ⟨C, hC, hBE⟩ := exists_bounded_convex_bound.{u}
  obtain ⟨q, hq, he⟩ := eventually_gaussian_lowerOrthant_pos S S₀
    (fun n => (hS n).posSemidef) hS₀ hlim a
  have he0 : Tendsto (fun n => C * (d : ℝ) ^ (1 / 4 : ℝ) *
      ((N n : ℝ) * (‖bentkusWhiteningCLM (S n)‖ * B n) ^ 3)) atTop (𝓝 0) := by
    simpa only [mul_zero] using herr.const_mul (C * (d : ℝ) ^ (1 / 4 : ℝ))
  have hsmall := he0.eventually (eventually_lt_nhds (by linarith : (0 : ℝ) < q / 2))
  refine ⟨q / 2, by linarith, ?_⟩
  filter_upwards [he, hsmall, ht] with n hn hsmall htn
  have hb := hBE hd (μ n) (X n) (S n) (B n) (hXm n) (hXB n) (hXi n) (hX0 n)
    (hS n) (hcov n) (lowerOrthant a) (measurableSet_lowerOrthant a) (convex_lowerOrthant a)
  have hl := (abs_le.mp hb).1
  have hq' : q / 2 ≤ ((μ n).map (fun ω ↦ ∑ i, X n i ω)).real (lowerOrthant a) := by
    nlinarith
  haveI : IsProbabilityMeasure ((μ n).map (fun ω ↦ ∑ i, X n i ω)) :=
    Measure.isProbabilityMeasure_map (Finset.measurable_sum _ (fun i _ => hXm n i)).aemeasurable
  exact hq'.trans (measureReal_mono (fun x hx i => (hx i).trans (htn i)))

end FCAppendix.BoundedVectorApproximation
