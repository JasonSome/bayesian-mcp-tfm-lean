import FCAppendix.Affine.Uniform06.ExactUntilting
import FCAppendix.Affine.Uniform06.WeightedReplacement
import FCAppendix.Affine.Uniform06.LiteralKernelIdentity
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section
namespace FCAppendix.Affine.Uniform06.SamplingCoefficientBounds

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology
open FCAppendix.Affine.WeightedSampling FCAppendix.ExponentialTilt
open MarkedRows

theorem selected_lower_marks_cancel {k N : ℕ}
    (fixed : Fin k → Pair) (row : Fin N → Pair) (cap : ℝ) :
    deficit cap (append fixed row) - (∑ j, ((1 : ℝ)/2-(fixed j).1)) =
      cap-(k : ℝ)/2-sumX row := by
  rw [deficit,sumX_append,Finset.sum_sub_distrib]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  unfold MarkedRows.sumX
  ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
lemma selectedSum_lower (h : ι → ℝ) {a : ℝ} (hh : ∀ j,a ≤ h j)
    (n : ℕ) (p : Path ι n) : (n : ℝ)*a ≤ selectedSum h n p := by
  induction n with
  | zero => simp [selectedSum]
  | succ n ih =>
    simp only [selectedSum,Nat.cast_add,Nat.cast_one]
    have ht := ih p.2
    have hh₀ := hh p.1
    nlinarith

theorem path_exponential_geometric_bound (w : Weights ι) (h : ι → ℝ)
    {a θ : ℝ} (hh : ∀ j,a ≤ h j) (hθ : 0 ≤ θ) (n : ℕ) (S : Finset ι) :
    0 ≤ (pathLaw w n S).expect (fun p => Real.exp (-θ*selectedSum h n p)) ∧
      (pathLaw w n S).expect (fun p => Real.exp (-θ*selectedSum h n p)) ≤
        (Real.exp (-θ*a))^n := by
  refine ⟨expect_nonneg _ _ (fun _ => (Real.exp_pos _).le),?_⟩
  apply expect_le_const
  intro p _
  have hh' := mul_le_mul_of_nonpos_left (selectedSum_lower h hh n p) (neg_nonpos.mpr hθ)
  calc
    Real.exp (-θ*selectedSum h n p) ≤ Real.exp (-θ*((n : ℝ)*a)) :=
      Real.exp_le_exp.mpr hh'
    _ = (Real.exp (-θ*a))^n := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring

theorem actual_removed_set_exponential_bound (w : Weights ι) (h : ι → ℝ)
    {a θ : ℝ} (hh : ∀ j,a ≤ h j) (hθ : 0 ≤ θ) (n : ℕ)
    (hW : (n : ℝ) < totalWeight w) :
    (pathLaw w n ∅).expect (fun p =>
      Real.exp (-θ*(∑ j ∈ finalSet n ∅ p,h j))) ≤ (Real.exp (-θ*a))^n := by
  calc
    _ = (pathLaw w n ∅).expect (fun p => Real.exp (-θ*selectedSum h n p)) := by
      apply LiteralKernelIdentity.expect_congr_on_positive_mass
      intro p hp
      have he := selectedSum_eq_setSum w h n ∅ (by simpa using hW) p hp
      simp only [Finset.sum_empty,sub_zero] at he
      rw [he]
    _ ≤ _ := (path_exponential_geometric_bound w h hh hθ n ∅).2

section Population
variable {Ω : Type*} [MeasurableSpace Ω]

theorem tilted_selected_coefficient_identity (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX : Measurable X)
    (hbX : ∀ᵐ ω ∂μ,X ω ∈ Icc (0 : ℝ) 1) (θ : ℝ) (w : Ω → ℝ) :
    (∫ ω,Real.exp (-θ*(1/2-X ω))*w ω ∂μ.tilted (fun x => -θ*X x)) =
      Real.exp (-θ/2-cgf X μ (-θ))*(∫ ω,w ω ∂μ) := by
  rw [integral_tilted_mul_eq_cgf _ (integrable_exp_mul_of_bounded μ hX.aemeasurable hbX (-θ)),
    ← integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ fun ω => by
    dsimp only
    rw [smul_eq_mul,← mul_assoc,← Real.exp_add]
    congr 2
    ring

def selectedRatio (μ : Measure Ω) (X w : Ω → ℝ) (θ : ℝ) : ℝ :=
  (∫ ω,Real.exp (-θ*(1/2-X ω))*w ω ∂μ.tilted (fun x => -θ*X x)) /
    (∫ ω,w ω ∂μ.tilted (fun x => -θ*X x))

theorem selectedRatio_original_formula (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX : Measurable X)
    (hbX : ∀ᵐ ω ∂μ,X ω ∈ Icc (0 : ℝ) 1) (θ : ℝ) (w : Ω → ℝ) :
    selectedRatio μ X w θ =
      Real.exp (-θ/2-cgf X μ (-θ))*(∫ ω,w ω ∂μ) /
        (∫ ω,w ω ∂μ.tilted (fun x => -θ*X x)) := by
  rw [selectedRatio,tilted_selected_coefficient_identity μ hX hbX]

theorem selectedRatio_geometric_bound (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X w : Ω → ℝ} (hX : Measurable X) (hw : Measurable w)
    (hbX : ∀ᵐ ω ∂μ,X ω ∈ Icc (0 : ℝ) 1)
    (hbw : ∀ᵐ ω ∂μ,w ω ∈ Icc (0 : ℝ) 1)
    {θ a : ℝ} (hθ : 0 < θ) (ha : 0 < a)
    (hgap : ∀ᵐ ω ∂μ.tilted (fun x => -θ*X x),0 < w ω → a ≤ 1/2-X ω)
    (hden : 0 < ∫ ω,w ω ∂μ.tilted (fun x => -θ*X x)) :
    0 ≤ selectedRatio μ X w θ ∧ selectedRatio μ X w θ ≤ Real.exp (-θ*a) ∧
      Real.exp (-θ*a) < 1 := by
  let ν := μ.tilted (fun x => -θ*X x)
  letI : IsProbabilityMeasure ν := isProbabilityMeasure_unitInterval_tilted μ hX hbX (-θ)
  have hXν : ∀ᵐ ω ∂ν,X ω ∈ Icc (0 : ℝ) 1 := unitInterval_tilted μ hbX (-θ)
  have hwν : ∀ᵐ ω ∂ν,w ω ∈ Icc (0 : ℝ) 1 := (tilted_absolutelyContinuous μ _).ae_le hbw
  have hwi : Integrable w ν := Integrable.of_mem_Icc 0 1 hw.aemeasurable hwν
  have hFi : Integrable (fun ω => Real.exp (-θ*(1/2-X ω))*w ω) ν := by
    apply Integrable.of_bound
      ((((measurable_const.sub hX).const_mul (-θ)).exp).mul hw).aestronglyMeasurable
      (Real.exp θ)
    filter_upwards [hXν,hwν] with ω hXω hwω
    dsimp only [Pi.mul_apply,Pi.sub_apply]
    rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le hwω.1)]
    calc
      _ ≤ Real.exp (-θ*(1/2-X ω))*1 :=
        mul_le_mul_of_nonneg_left hwω.2 (Real.exp_pos _).le
      _ ≤ Real.exp θ := by
        rw [mul_one]
        apply Real.exp_le_exp.mpr
        have hh := mul_le_mul_of_nonneg_left hXω.2 hθ.le
        nlinarith [hh]
  have hnum0 : 0 ≤ ∫ ω,Real.exp (-θ*(1/2-X ω))*w ω ∂ν :=
    integral_nonneg_of_ae (hwν.mono fun ω hω => mul_nonneg (Real.exp_pos _).le hω.1)
  have hnum : (∫ ω,Real.exp (-θ*(1/2-X ω))*w ω ∂ν) ≤
      Real.exp (-θ*a)*(∫ ω,w ω ∂ν) := by
    rw [← integral_const_mul]
    apply integral_mono_ae hFi (hwi.const_mul _)
    filter_upwards [hwν,hgap] with ω hwω hω
    by_cases hw0 : w ω=0
    · simp [hw0]
    · apply mul_le_mul_of_nonneg_right _ hwω.1
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonpos_left (hω (lt_of_le_of_ne hwω.1 (Ne.symm hw0)))
        (neg_nonpos.mpr hθ.le)
  refine ⟨div_nonneg hnum0 hden.le,?_,?_⟩
  · exact (div_le_iff₀ hden).mpr hnum
  · apply Real.exp_lt_one_iff.mpr
    nlinarith [mul_pos hθ ha]

end Population

def coefficient (γ : ℕ → ℝ) : ℝ := 1+∑' n : ℕ,γ (n+1)

theorem coefficient_positive_bounded {γ : ℕ → ℝ} {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hγ : ∀ n,0 ≤ γ (n+1) ∧ γ (n+1) ≤ 2*q^(n+1)) :
    Summable (fun n => γ (n+1)) ∧
      1 ≤ coefficient γ ∧ coefficient γ ≤ 1+2*q/(1-q) := by
  have hgeo : HasSum (fun n : ℕ => 2*q^(n+1)) (2*q/(1-q)) := by
    simpa only [pow_succ',div_eq_mul_inv,mul_assoc] using
      (hasSum_geometric_of_lt_one hq0 hq1).mul_left (2*q)
  have hs : Summable (fun n => γ (n+1)) := Summable.of_nonneg_of_le
    (fun n => (hγ n).1) (fun n => (hγ n).2) hgeo.summable
  refine ⟨hs,?_,?_⟩
  · unfold coefficient
    have hh : (0:ℝ) ≤ ∑' n : ℕ, γ (n+1) := tsum_nonneg (fun n => (hγ n).1)
    linarith
  · unfold coefficient
    have hh := hs.tsum_le_tsum (fun n => (hγ n).2) hgeo.summable
    rw [hgeo.tsum_eq] at hh
    linarith

theorem coefficient_tail_bound {γ : ℕ → ℝ} {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hγ : ∀ n,0 ≤ γ (n+1) ∧ γ (n+1) ≤ 2*q^(n+1)) (K : ℕ) :
    0 ≤ (∑' n : ℕ,γ (n+K+1)) ∧
      (∑' n : ℕ,γ (n+K+1)) ≤ 2*q^(K+1)/(1-q) := by
  have hgeo : HasSum (fun n : ℕ => 2*q^(n+K+1)) (2*q^(K+1)/(1-q)) := by
    convert! (hasSum_geometric_of_lt_one hq0 hq1).mul_left (2*q^(K+1)) using 1
    · funext n
      rw [show n+K+1=(K+1)+n by omega,pow_add]
      ring
  have hs : Summable (fun n => γ (n+K+1)) := Summable.of_nonneg_of_le
    (fun n => (hγ (n+K)).1) (fun n => (hγ (n+K)).2) hgeo.summable
  refine ⟨tsum_nonneg (fun n => (hγ (n+K)).1),?_⟩
  exact (hs.tsum_le_tsum (fun n => (hγ (n+K)).2) hgeo.summable).trans_eq hgeo.tsum_eq

end FCAppendix.Affine.Uniform06.SamplingCoefficientBounds
