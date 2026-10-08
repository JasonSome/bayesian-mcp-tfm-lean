import FCAppendix.PayOnce.KernelEntryExpansion
import FCAppendix.PayOnce.KernelTaylor

namespace FCAppendix.PayOnce.KernelEntryExpectation
open MeasureTheory ProbabilityTheory Set Filter Topology Real CommonList
open KernelTailEvent KernelLawConvergence KernelEntryExpansion KernelTaylor

theorem entry_remainder_le_center (b L a t : ℝ) :
    (b-L)^2+|L-t| *|b-L| ≤
      4*((b-a)^2+(L-a)^2)+|a-t| *(|b-a|+|L-a|) := by
  have hd : |b-L| ≤ |b-a|+|L-a| := by
    simpa only [abs_sub_comm a L] using abs_sub_le b a L
  have hL : |L-t| ≤ |L-a|+|a-t| := abs_sub_le L a t
  have hs := pow_le_pow_left₀ (abs_nonneg (b-L)) hd 2
  have hm := mul_le_mul hL hd (abs_nonneg _) (by positivity : 0 ≤ |L-a|+|a-t|)
  rw [sq_abs] at hs
  nlinarith [sq_nonneg (|b-a|-|L-a|),sq_abs (b-a),sq_abs (L-a)]

theorem exists_test_entry_expansion {n : ℕ} (hn : 2 ≤ n) {t : ℝ} (ht : 0 < t)
    (ψ : ℝ → ℝ) (d K : ℝ) (hK : 0 ≤ K)
    (hψ : ∀ p ∈ Icc (0:ℝ) 1, |ψ p-d*p| ≤ K*p^2) :
    ∃ C : ℝ, 0 < C ∧ ∀ b ∈ Icc (3*t/4) (5*t/4),
      ∀ L ∈ Icc (3*t/4) (5*t/4),
        |ψ (kernel n b L)-(d*(2/(((n:ℝ)-1)*t)))*max (b-L) 0| ≤
          C*((b-L)^2+|L-t| *|b-L|) := by
  obtain ⟨C,hC,hentry⟩ := exists_kernel_entry_expansion hn ht
  let U : ℝ := (n:ℝ)/(t/2)
  refine ⟨K*U^2+|d| *C+1,by positivity,?_⟩
  intro b hb L hL
  have hLp : 0 < L := by linarith [hL.1]
  have hp := kernel_bounds hn hLp b
  have hk : |kernel n b L| ≤ U*|b-L| := by
    have hh := kernel_price_difference hn (by positivity : 0 < t/2)
      (by linarith [hL.1] : t/2 ≤ L) (by linarith [hb.1] : t/2 ≤ b) b
    simpa only [kernel_of_le n le_rfl,sub_zero,abs_sub_comm L b] using hh
  have hk2 : (kernel n b L)^2 ≤ U^2*(b-L)^2 := by
    have hh := pow_le_pow_left₀ (abs_nonneg _) hk 2
    simpa only [mul_pow,sq_abs] using hh
  have hfirst := (hψ _ hp).trans (mul_le_mul_of_nonneg_left hk2 hK)
  have hsecond := mul_le_mul_of_nonneg_left (hentry b hb L hL) (abs_nonneg d)
  have he : ψ (kernel n b L)-(d*(2/(((n:ℝ)-1)*t)))*max (b-L) 0 =
      (ψ (kernel n b L)-d*kernel n b L)+
        d*(kernel n b L-(2/(((n:ℝ)-1)*t))*max (b-L) 0) := by ring
  rw [he]
  have hsecond' : |d*(kernel n b L-(2/(((n:ℝ)-1)*t))*max (b-L) 0)| ≤
      |d| *(C*((b-L)^2+|L-t| *|b-L|)) := by
    simpa only [abs_mul] using hsecond
  have hh := (abs_add_le _ _).trans (add_le_add hfirst hsecond')
  apply hh.trans
  have hR : 0 ≤ |L-t| *|b-L| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
  nlinarith [sq_nonneg (b-L),mul_nonneg (mul_nonneg hK (sq_nonneg U)) hR]

universe u

theorem integral_entry_error_le {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ} (hn : 2 ≤ n)
    {t : ℝ} (ht : 0 < t) (X : Ω → ℝ) (hX : Measurable X)
    (hXI : ∀ z, X z ∈ Icc (3*t/4) (5*t/4))
    (ψ : ℝ → ℝ) (hψ : Measurable ψ) {B : ℝ}
    (hB : ∀ p ∈ Icc (0:ℝ) 1, |ψ p| ≤ B)
    {C α b : ℝ} (hC : 0 ≤ C) (hb : b ∈ Icc (3*t/4) (5*t/4))
    (hentry : ∀ L ∈ Icc (3*t/4) (5*t/4),
      |ψ (kernel n b L)-α*max (b-L) 0| ≤ C*((b-L)^2+|L-t| *|b-L|))
    (a : ℝ) :
    |(∫ z, ψ (kernel n b (X z)) ∂μ)-α*(∫ z, max (b-X z) 0 ∂μ)| ≤
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
  have hh := (abs_integral_le_integral_abs
    (f := fun z => ψ (kernel n b (X z))-α*max (b-X z) 0)).trans
    (integral_mono (hψi.sub (hpos.const_mul α)).abs hbinti hbound)
  rw [integral_sub hψi (hpos.const_mul α),integral_const_mul] at hh
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

end FCAppendix.PayOnce.KernelEntryExpectation
