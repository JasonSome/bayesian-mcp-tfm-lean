import FCAppendix.Affine.Tail04.SourceTailCapGap
import FCAppendix.Affine.Tail04.SourceBulkAnalyticAdapter

noncomputable section
namespace FCAppendix.Affine.Tail04.SourceTailNoisyGap
open MeasureTheory ProbabilityTheory Set Classical
open OriginalValues SourceMenuIdentity SourceTailTaylor SourceTailCapGap
open FiniteTailNoisyGame SourceTailNoisyFixedPoint

variable (D : Data) (P : ValueParameters) (t : ℝ)
  (Amin Amax k lamA lamR : ℝ)
  (hξh : D.ξ≤1/2) (hmin : 0< Amin)
  (hA : Amin≤ leadingA P D.ξ lamA lamR) (hmax : leadingA P D.ξ lamA lamR≤ Amax)
  (hk : k<1/(2*Amax)) (ht : 0< t)
  (hF : D.F=Central.B D.ξ) (hcap : D.U=Central.B D.ξ-k/t)
  (hleft : endpointRadius Amin/t≤ Central.B D.ξ-1)

def inwardBid : Icc (1:ℝ) D.U := by
  let A := leadingA P D.ξ lamA lamR
  have hd := coefficient_distance hmin hA hmax hk
  have ha : 0< A := hmin.trans_le hA
  have hrad := div_le_div_of_nonneg_right hd.2.2.2 ht.le
  have he : (1/(2*A))/t=1/(2*A*t) := by ring
  change (1/(2*A))/t≤ endpointRadius Amin/t at hrad
  rw [he] at hrad
  have hkA : k<1/(2*A) := by linarith [hd.1,hd.2.1]
  have hkAt := div_lt_div_of_pos_right hkA ht
  rw [he] at hkAt
  refine ⟨comparison (Central.B D.ξ) A t,?_,?_⟩
  · unfold comparison
    linarith
  · rw [hcap]
    unfold comparison
    linarith

include hF in
lemma physical_mem (b : Icc (1:ℝ) D.U) (z : unitInterval) :
    (b:ℝ)*(1+D.eps*(z:ℝ))∈Icc (1:ℝ) (Central.B D.ξ) := by
  have hp : 0≤(b:ℝ) := (by norm_num : (0:ℝ)≤1).trans b.2.1
  have hz : 0≤ D.eps*(z:ℝ) := mul_nonneg D.heps.le z.2.1
  constructor
  · nlinarith [mul_nonneg hp hz,b.2.1]
  · calc
      _ ≤ (b:ℝ)*(1+D.eps) := mul_le_mul_of_nonneg_left (by nlinarith [D.heps,z.2.2]) hp
      _ ≤ D.U*(1+D.eps) := mul_le_mul_of_nonneg_right b.2.2 (by linarith [D.heps])
      _ ≤ Central.B D.ξ := by simpa only [hF] using D.hUF

include hξh hF in
theorem pointwise_gap
    (hlamA0 : (1-D.ξ)*Central.B D.ξ≤ lamA) (hlamA1 : lamA≤1)
    (hlamR0 : (1-D.ξ)*Central.B D.ξ≤ lamR) (hlamR1 : lamR≤1)
    (hbudget : 2*taylorConstant D.ξ (endpointRadius Amin)/t^2≤
      Amin*(stripWidth Amax k)^2/(4*t))
    (hnoise : D.eps*D.U≤ stripWidth Amax k/(4*t))
    (v : ℝ) (hvt : v≤ t) (b : Icc (1:ℝ) D.U)
    (hb : inwardCut (Central.B D.ξ) Amax k t≤(b:ℝ)) (z : unitInterval) :
    Amin*(stripWidth Amax k)^2/(2*t)≤
      menuUtility P D.ξ lamA lamR v
        ((inwardBid D P t Amin Amax k lamA lamR hmin hA hmax hk ht hcap hleft:ℝ)*
          (1+D.eps*(z:ℝ)))-
      menuUtility P D.ξ lamA lamR v ((b:ℝ)*(1+D.eps*(z:ℝ))) := by
  let y := inwardBid D P t Amin Amax k lamA lamR hmin hA hmax hk ht hcap hleft
  have hz : 0≤ D.eps*(z:ℝ) := mul_nonneg D.heps.le z.2.1
  have hy0 : 0≤(y:ℝ) := (by norm_num : (0:ℝ)≤1).trans y.2.1
  have hyshift : 0≤(y:ℝ)*D.eps*(z:ℝ) ∧
      (y:ℝ)*D.eps*(z:ℝ)≤ stripWidth Amax k/(4*t) := by
    constructor
    · exact mul_nonneg (mul_nonneg hy0 D.heps.le) z.2.1
    · calc
        _ ≤ (y:ℝ)*D.eps := by nlinarith [z.2.2,mul_nonneg hy0 D.heps.le]
        _ ≤ D.eps*D.U := by nlinarith [mul_le_mul_of_nonneg_right y.2.2 D.heps.le]
        _ ≤ stripWidth Amax k/(4*t) := hnoise
  have hcompare : (y:ℝ)*(1+D.eps*(z:ℝ))∈
      Icc (comparison (Central.B D.ξ) (leadingA P D.ξ lamA lamR) t)
        (comparison (Central.B D.ξ) (leadingA P D.ξ lamA lamR) t+stripWidth Amax k/(4*t)) := by
    change (y:ℝ)≤(y:ℝ)*(1+D.eps*(z:ℝ)) ∧
      (y:ℝ)*(1+D.eps*(z:ℝ))≤(y:ℝ)+stripWidth Amax k/(4*t)
    constructor <;> nlinarith
  have hbphys : inwardCut (Central.B D.ξ) Amax k t≤(b:ℝ)*(1+D.eps*(z:ℝ)) := by
    have hb0 : 0≤(b:ℝ) := (by norm_num : (0:ℝ)≤1).trans b.2.1
    nlinarith [mul_nonneg hb0 hz]
  exact analytic_strip_gap P D.hξ hξh hmin hA hmax hk ht hvt
    (physical_mem D hF y z) (physical_mem D hF b z) hbphys hcompare
    hlamA0 hlamA1 hlamR0 hlamR1 hbudget

include hξh hF in
theorem averaged_gap
    (hlamA0 : (1-D.ξ)*Central.B D.ξ≤ lamA) (hlamA1 : lamA≤1)
    (hlamR0 : (1-D.ξ)*Central.B D.ξ≤ lamR) (hlamR1 : lamR≤1)
    (hbudget : 2*taylorConstant D.ξ (endpointRadius Amin)/t^2≤
      Amin*(stripWidth Amax k)^2/(4*t))
    (hnoise : D.eps*D.U≤ stripWidth Amax k/(4*t))
    (v : ℝ) (hvt : v≤ t) (b : Icc (1:ℝ) D.U)
    (hb : inwardCut (Central.B D.ξ) Amax k t≤(b:ℝ)) :
    Amin*(stripWidth Amax k)^2/(2*t)≤
      (∫ z : unitInterval,menuUtility P D.ξ lamA lamR v
        ((inwardBid D P t Amin Amax k lamA lamR hmin hA hmax hk ht hcap hleft:ℝ)*
          (1+D.eps*(z:ℝ))))-
      (∫ z : unitInterval,menuUtility P D.ξ lamA lamR v ((b:ℝ)*(1+D.eps*(z:ℝ)))) := by
  let y := inwardBid D P t Amin Amax k lamA lamR hmin hA hmax hk ht hcap hleft
  have hc (b' : Icc (1:ℝ) D.U) : Continuous
      (fun z : unitInterval=> menuUtility P D.ξ lamA lamR v ((b':ℝ)*(1+D.eps*(z:ℝ)))) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    exact (SourceBulkAnalyticAdapter.differentiableAt_menu P D.ξ lamA lamR v _
      (by have hh := (physical_mem D hF b' z).1;linarith)).continuousAt.comp (by fun_prop)
  have hy := (hc y).integrable_of_hasCompactSupport (μ := (volume : Measure unitInterval))
    (HasCompactSupport.of_compactSpace _)
  have hb' := (hc b).integrable_of_hasCompactSupport (μ := (volume : Measure unitInterval))
    (HasCompactSupport.of_compactSpace _)
  have hh := integral_mono (integrable_const (Amin*(stripWidth Amax k)^2/(2*t))) (hy.sub hb')
    (fun z=> pointwise_gap D P t Amin Amax k lamA lamR hξh hmin hA hmax hk ht hF hcap hleft
      hlamA0 hlamA1 hlamR0 hlamR1 hbudget hnoise v hvt b hb z)
  simp only [Pi.sub_apply] at hh
  rw [integral_sub hy hb'] at hh
  simpa only [integral_const,probReal_univ,one_smul] using hh

end FCAppendix.Affine.Tail04.SourceTailNoisyGap
