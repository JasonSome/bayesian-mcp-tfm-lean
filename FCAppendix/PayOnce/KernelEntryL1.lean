import FCAppendix.PayOnce.ScaledEntryExpectation

namespace FCAppendix.PayOnce.KernelEntryExpectation
open MeasureTheory ProbabilityTheory Set Filter Topology Real CommonList
open KernelTailEvent KernelLawConvergence KernelEntryExpansion KernelTaylor

theorem integral_abs_entry_error_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ} (hn : 2 ≤ n)
    {t : ℝ} (ht : 0 < t) (X : Ω → ℝ) (hX : Measurable X)
    (hXI : ∀ z, X z ∈ Icc (3*t/4) (5*t/4))
    (ψ : ℝ → ℝ) (hψ : Measurable ψ) {B : ℝ}
    (hB : ∀ p ∈ Icc (0:ℝ) 1, |ψ p| ≤ B)
    {C α b : ℝ} (hC : 0 ≤ C) (hb : b ∈ Icc (3*t/4) (5*t/4))
    (hentry : ∀ L ∈ Icc (3*t/4) (5*t/4),
      |ψ (kernel n b L)-α*max (b-L) 0| ≤ C*((b-L)^2+|L-t| *|b-L|))
    (a : ℝ) :
    (∫ z, |ψ (kernel n b (X z))-α*max (b-X z) 0| ∂μ) ≤
      C*(4*((b-a)^2+(∫ z, (X z-a)^2 ∂μ))+
        |a-t| *(|b-a|+(∫ z, |X z-a| ∂μ))) := by
  have hbp : 0 < b := by linarith [hb.1]
  have hXp (z : Ω) : 0 < X z := by linarith [(hXI z).1]
  have hXLp : MemLp X 2 μ := memLp_of_bounded (.of_forall hXI) hX.aestronglyMeasurable _
  have hXLpi : Integrable X μ := hXLp.integrable (by norm_num)
  have hX2 : Integrable (fun z => (X z-a)^2) μ :=
    (hXLp.sub (memLp_const a)).integrable_sq
  have hXabs : Integrable (fun z => |X z-a|) μ :=
    (hXLpi.sub (integrable_const a)).abs
  have hpos : Integrable (fun z => max (b-X z) 0) μ :=
    ((integrable_const b).sub hXLpi).sup (integrable_const 0)
  have hψi : Integrable (fun z => ψ (kernel n b (X z))) μ :=
    Integrable.of_bound (hψ.comp (measurable_kernel_of_positive_price hn hbp hX hXp)).aestronglyMeasurable
      B (.of_forall fun z => by simpa only [Real.norm_eq_abs] using hB _ (kernel_bounds hn (hXp z) b))
  have hbound (z : Ω) : |ψ (kernel n b (X z))-α*max (b-X z) 0| ≤
      C*(4*((b-a)^2+(X z-a)^2)+|a-t| *(|b-a|+|X z-a|)) :=
    (hentry (X z) (hXI z)).trans (mul_le_mul_of_nonneg_left
      (entry_remainder_le_center b (X z) a t) hC)
  have hbinti : Integrable (fun z => C*(4*((b-a)^2+(X z-a)^2)+
      |a-t| *(|b-a|+|X z-a|))) μ :=
    (((integrable_const _).add hX2).const_mul 4 |>.add
      (((integrable_const _).add hXabs).const_mul |a-t|)).const_mul C
  have hh := integral_mono (hψi.sub (hpos.const_mul α)).abs hbinti hbound
  have he : (∫ z, C*(4*((b-a)^2+(X z-a)^2)+|a-t| *(|b-a|+|X z-a|)) ∂μ) =
      C*(4*((b-a)^2+(∫ z, (X z-a)^2 ∂μ))+|a-t| *(|b-a|+(∫ z, |X z-a| ∂μ))) := by
    have hsq : Integrable (fun z => 4*((b-a)^2+(X z-a)^2)) μ :=
      ((integrable_const _).add hX2).const_mul 4
    have hab : Integrable (fun z => |a-t| *(|b-a|+|X z-a|)) μ :=
      ((integrable_const _).add hXabs).const_mul |a-t|
    rw [integral_const_mul,integral_add hsq hab,integral_const_mul,integral_const_mul,
      integral_add (integrable_const _) hX2,integral_add (integrable_const _) hXabs]
    simp only [integral_const,probReal_univ,one_smul]
  exact hh.trans_eq he

theorem normalized_integral_abs_entry_error_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ} (hn : 2 ≤ n)
    {t : ℝ} (ht : 0 < t) (X : Ω → ℝ) (hX : Measurable X)
    (hXI : ∀ z, X z ∈ Icc (3*t/4) (5*t/4))
    (ψ : ℝ → ℝ) (hψ : Measurable ψ) {B : ℝ}
    (hB : ∀ p ∈ Icc (0:ℝ) 1, |ψ p| ≤ B)
    {C α a s y K : ℝ} (hC : 0 ≤ C) (hs : 0 < s)
    (hb : a+s*y ∈ Icc (3*t/4) (5*t/4))
    (hentry : ∀ L ∈ Icc (3*t/4) (5*t/4),
      |ψ (kernel n (a+s*y) L)-α*max (a+s*y-L) 0| ≤ C*((a+s*y-L)^2+|L-t| *|a+s*y-L|))
    (hK : (∫ z, ((X z-a)/s)^2 ∂μ) ≤ K) :
    (∫ z, |ψ (kernel n (a+s*y) (X z))/s-α*max (y-(X z-a)/s) 0| ∂μ) ≤
      C*(4*s*(y^2+K)+|a-t| *(|y|+1+K)) := by
  let Z := fun z => (X z-a)/s
  have hLp : MemLp Z 2 μ := by
    have hh : MemLp (fun z => s⁻¹*(X z-a)) 2 μ :=
      ((memLp_of_bounded (.of_forall hXI) hX.aestronglyMeasurable 2).sub (memLp_const a)).const_mul s⁻¹
    simpa only [Z,div_eq_mul_inv,mul_comm] using hh
  have hfirst : (∫ z, |Z z| ∂μ) ≤ 1+K := integral_abs_le_one_add_secondMoment μ hLp hK
  have hXid z : X z-a = s*Z z := by dsimp only [Z]; field_simp
  have h2 : (∫ z, (X z-a)^2 ∂μ) = s^2*(∫ z, (Z z)^2 ∂μ) := by
    simp_rw [hXid,mul_pow]
    exact integral_const_mul _ _
  have h1 : (∫ z, |X z-a| ∂μ) = s*(∫ z, |Z z| ∂μ) := by
    simp_rw [hXid,abs_mul,abs_of_pos hs]
    exact integral_const_mul _ _
  have hpos z : max (a+s*y-X z) 0 = s*max (y-Z z) 0 := by
    rw [mul_max_of_nonneg _ _ hs.le,mul_zero]
    congr 1
    nlinarith [hXid z]
  have hh := integral_abs_entry_error_le μ hn ht X hX hXI ψ hψ hB hC hb hentry a
  rw [h2,h1,show a+s*y-a=s*y by ring,mul_pow,abs_mul,abs_of_pos hs] at hh
  have hsecond : s^2*(∫ z, (Z z)^2 ∂μ) ≤ s^2*K := mul_le_mul_of_nonneg_left hK (sq_nonneg s)
  have hfirst' : s*(∫ z, |Z z| ∂μ) ≤ s*(1+K) := mul_le_mul_of_nonneg_left hfirst hs.le
  have hbound : (∫ z, |ψ (kernel n (a+s*y) (X z))-α*max (a+s*y-X z) 0| ∂μ) ≤
      s*(C*(4*s*(y^2+K)+|a-t| *(|y|+1+K))) := by
    apply hh.trans
    calc
      _ ≤ C*(4*(s^2*y^2+s^2*K)+|a-t| *(s*|y|+s*(1+K))) := by
        apply mul_le_mul_of_nonneg_left _ hC
        exact add_le_add (mul_le_mul_of_nonneg_left (add_le_add le_rfl hsecond) (by norm_num))
          (mul_le_mul_of_nonneg_left (add_le_add le_rfl hfirst') (abs_nonneg _))
      _ = _ := by ring
  have hd := (div_le_iff₀ hs).mpr (show
      (∫ z, |ψ (kernel n (a+s*y) (X z))-α*max (a+s*y-X z) 0| ∂μ) ≤
      (C*(4*s*(y^2+K)+|a-t| *(|y|+1+K)))*s by simpa only [mul_comm] using hbound)
  have he : (∫ z, |ψ (kernel n (a+s*y) (X z))/s-α*max (y-Z z) 0| ∂μ) =
      (∫ z, |ψ (kernel n (a+s*y) (X z))-α*max (a+s*y-X z) 0| ∂μ)/s := by
    rw [← integral_div]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro z
    change |ψ (kernel n (a+s*y) (X z))/s-α*max (y-Z z) 0| =
      |ψ (kernel n (a+s*y) (X z))-α*max (a+s*y-X z) 0|/s
    have hq : ψ (kernel n (a+s*y) (X z))/s-α*max (y-Z z) 0 =
        (ψ (kernel n (a+s*y) (X z))-α*max (a+s*y-X z) 0)/s := by
      rw [hpos]
      field_simp
    rw [hq,abs_div,abs_of_pos hs]
  change (∫ z, |ψ (kernel n (a+s*y) (X z))/s-α*max (y-Z z) 0| ∂μ) ≤ _
  rw [he]
  exact hd

end FCAppendix.PayOnce.KernelEntryExpectation
