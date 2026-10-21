import FCAppendix.Affine.Tail04.SourceMenuIdentity
import FCAppendix.Affine.Tail04.SourceTailNoisyFixedPoint
import Mathlib.Analysis.Calculus.MeanValue

noncomputable section
namespace FCAppendix.Affine.Tail04.SourceBulkAnalyticAdapter
open MeasureTheory ProbabilityTheory Set Classical
open OriginalValues SourceMenuIdentity FiniteTailNoisyGame SourceTailNoisyFixedPoint

def BulkDerivativeBound (P : ValueParameters) (ξ κ : ℝ) (Λ : Set (ℝ×ℝ)) : Prop :=
  ∀ lam∈Λ,∀ v∈Icc (P.vA-P.w) (P.vA+P.w),∀ b∈Icc (1:ℝ) (Central.B ξ),
    deriv (menuUtility P ξ lam.1 lam.2 v) b≤-κ

lemma differentiableAt_menu (P : ValueParameters) (ξ lamA lamR v b : ℝ) (hb : b≠0) :
    DifferentiableAt ℝ (menuUtility P ξ lamA lamR v) b := by
  unfold menuUtility payment served duplicates mixedProbability exposure
  fun_prop (disch := exact hb)

theorem source_slope (P : ValueParameters) {ξ κ : ℝ} {Λ : Set (ℝ×ℝ)}
    (hder : BulkDerivativeBound P ξ κ Λ) (lam : ℝ×ℝ) (hlam : lam∈Λ)
    (v : ℝ) (hv : v∈Icc (P.vA-P.w) (P.vA+P.w))
    (a b : ℝ) (ha : a∈Icc (1:ℝ) (Central.B ξ))
    (hb : b∈Icc (1:ℝ) (Central.B ξ)) (hab : a≤ b) :
    κ*(b-a)≤ menuUtility P ξ lam.1 lam.2 v a-menuUtility P ξ lam.1 lam.2 v b := by
  have hd (x : ℝ) (hx : x∈Icc (1:ℝ) (Central.B ξ)) :
      DifferentiableAt ℝ (menuUtility P ξ lam.1 lam.2 v) x :=
    differentiableAt_menu P ξ lam.1 lam.2 v x (by linarith [hx.1])
  have hc : ContinuousOn (menuUtility P ξ lam.1 lam.2 v) (Icc (1:ℝ) (Central.B ξ)) :=
    fun x hx=>(hd x hx).continuousAt.continuousWithinAt
  have hi : DifferentiableOn ℝ (menuUtility P ξ lam.1 lam.2 v)
      (interior (Icc (1:ℝ) (Central.B ξ))) :=
    fun x hx=>(hd x (interior_subset hx)).differentiableWithinAt
  have hh := (convex_Icc (1:ℝ) (Central.B ξ)).image_sub_le_mul_sub_of_deriv_le hc hi
    (fun x hx=> hder lam hlam v hv x (interior_subset hx)) a ha b hb hab
  linarith

def bottom (D : Data) : Icc (1:ℝ) (1+D.u) := ⟨1,le_rfl,by linarith [D.hu]⟩

lemma physical_bulk_mem (D : Data) (hF : D.F=Central.B D.ξ)
    (b : Icc (1:ℝ) (1+D.u)) (z : unitInterval) :
    (b:ℝ)*(1+D.eps*(z:ℝ))∈Icc (1:ℝ) (Central.B D.ξ) := by
  have hpos : 0≤(b:ℝ) := (by norm_num : (0:ℝ)≤1).trans b.2.1
  have hn0 : 0≤ D.eps*(z:ℝ) := mul_nonneg D.heps.le z.2.1
  have hn1 : D.eps*(z:ℝ)≤ D.eps := by nlinarith [D.heps,z.2.2]
  constructor
  · nlinarith [mul_nonneg hpos hn0,b.2.1]
  · calc
      _ ≤ (b:ℝ)*(1+D.eps) := mul_le_mul_of_nonneg_left (by linarith) hpos
      _ ≤ D.U*(1+D.eps) := mul_le_mul_of_nonneg_right (b.2.2.trans D.huU) (by linarith [D.heps])
      _ ≤ Central.B D.ξ := by simpa only [hF] using D.hUF

theorem noisy_top_half_gap (D : Data) (P : ValueParameters)
    (hF : D.F=Central.B D.ξ) {κ : ℝ} (hκ : 0≤ κ) {Λ : Set (ℝ×ℝ)}
    (hder : BulkDerivativeBound P D.ξ κ Λ) (lam : ℝ×ℝ) (hlam : lam∈Λ)
    (v : Icc (P.vA-P.w) (P.vA+P.w))
    (b : Icc (1:ℝ) (1+D.u)) (hb : 1+D.u/2≤(b:ℝ)) (z : unitInterval) :
    κ*D.u/2≤
      menuUtility P D.ξ lam.1 lam.2 v (1+D.eps*(z:ℝ))-
      menuUtility P D.ξ lam.1 lam.2 v ((b:ℝ)*(1+D.eps*(z:ℝ))) := by
  have hn : 0≤ D.eps*(z:ℝ) := mul_nonneg D.heps.le z.2.1
  have hd : D.u/2≤(b:ℝ)*(1+D.eps*(z:ℝ))-(1+D.eps*(z:ℝ)) := by
    have hh : 0≤(b:ℝ)-1 := by linarith [b.2.1]
    nlinarith [mul_nonneg hh hn]
  have ha := physical_bulk_mem D hF (bottom D) z
  simp only [bottom,Subtype.coe_mk,one_mul] at ha
  have hh := source_slope P hder lam hlam v v.2
    (1+D.eps*(z:ℝ)) ((b:ℝ)*(1+D.eps*(z:ℝ))) ha
    (physical_bulk_mem D hF b z) (by linarith [D.hu])
  have hs := mul_le_mul_of_nonneg_left hd hκ
  nlinarith

theorem averaged_noisy_top_half_gap (D : Data) (P : ValueParameters)
    (hF : D.F=Central.B D.ξ) {κ : ℝ} (hκ : 0≤ κ) {Λ : Set (ℝ×ℝ)}
    (hder : BulkDerivativeBound P D.ξ κ Λ) (lam : ℝ×ℝ) (hlam : lam∈Λ)
    (v : Icc (P.vA-P.w) (P.vA+P.w))
    (b : Icc (1:ℝ) (1+D.u)) (hb : 1+D.u/2≤(b:ℝ)) :
    κ*D.u/2≤
      (∫ z : unitInterval,menuUtility P D.ξ lam.1 lam.2 v (1+D.eps*(z:ℝ)))-
      (∫ z : unitInterval,menuUtility P D.ξ lam.1 lam.2 v ((b:ℝ)*(1+D.eps*(z:ℝ)))) := by
  have hc (b' : Icc (1:ℝ) (1+D.u)) : Continuous
      (fun z : unitInterval=> menuUtility P D.ξ lam.1 lam.2 v ((b':ℝ)*(1+D.eps*(z:ℝ)))) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    exact (differentiableAt_menu P D.ξ lam.1 lam.2 v _
      (by have hh:=(physical_bulk_mem D hF b' z).1;linarith)).continuousAt.comp
        (by fun_prop)
  have ha := (hc (bottom D)).integrable_of_hasCompactSupport
    (μ := (volume : Measure unitInterval)) (HasCompactSupport.of_compactSpace _)
  have hb' := (hc b).integrable_of_hasCompactSupport
    (μ := (volume : Measure unitInterval)) (HasCompactSupport.of_compactSpace _)
  have hh := integral_mono (integrable_const (κ*D.u/2)) (ha.sub hb')
    (fun z=> by
      simpa only [Pi.sub_apply,bottom,Subtype.coe_mk,one_mul] using
        noisy_top_half_gap D P hF hκ hder lam hlam v b hb z)
  simp only [Pi.sub_apply] at hh
  rw [integral_sub ha hb'] at hh
  simpa only [integral_const,probReal_univ,one_smul,bottom,Subtype.coe_mk,one_mul] using hh

end FCAppendix.Affine.Tail04.SourceBulkAnalyticAdapter
