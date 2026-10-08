import FCAppendix.PayOnce.KernelEntryExpectation

namespace FCAppendix.PayOnce.KernelEntryExpectation
open MeasureTheory ProbabilityTheory Set Filter Topology Real CommonList KernelTaylor KernelTailEvent

theorem integral_abs_le_one_add_secondMoment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {Z : Ω → ℝ} (hZ : MemLp Z 2 μ)
    {K : ℝ} (hK : (∫ z, (Z z)^2 ∂μ) ≤ K) : (∫ z, |Z z| ∂μ) ≤ 1+K := by
  have hi := hZ.integrable (by norm_num)
  have hh := integral_mono hi.abs ((integrable_const 1).add hZ.integrable_sq)
    (fun z => by change |Z z| ≤ 1+(Z z)^2; nlinarith [sq_nonneg (|Z z|-1),sq_abs (Z z)])
  simp only [Pi.add_apply] at hh
  rw [integral_add (integrable_const 1) hZ.integrable_sq] at hh
  simp only [integral_const,probReal_univ,one_smul] at hh
  linarith

theorem normalized_integral_entry_error_le {Ω : Type*} [MeasurableSpace Ω]
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
    |(∫ z, ψ (kernel n (a+s*y) (X z)) ∂μ)/s-
      α*(∫ z, max (y-(X z-a)/s) 0 ∂μ)| ≤
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
  have hpos : (∫ z, max (a+s*y-X z) 0 ∂μ) = s*(∫ z, max (y-Z z) 0 ∂μ) := by
    calc
      _ = ∫ z, s*max (y-Z z) 0 ∂μ := by
        apply integral_congr_ae
        apply Filter.Eventually.of_forall
        intro z
        change max (a+s*y-X z) 0 = s*max (y-Z z) 0
        rw [mul_max_of_nonneg _ _ hs.le,mul_zero]
        congr 1
        nlinarith [hXid z]
      _ = _ := integral_const_mul _ _
  have hh := integral_entry_error_le μ hn ht X hX hXI ψ hψ hB hC hb hentry a
  rw [h2,h1,hpos,show a+s*y-a=s*y by ring,mul_pow,abs_mul,abs_of_pos hs] at hh
  have hsecond : s^2*(∫ z, (Z z)^2 ∂μ) ≤ s^2*K := mul_le_mul_of_nonneg_left hK (sq_nonneg s)
  have hfirst' : s*(∫ z, |Z z| ∂μ) ≤ s*(1+K) := mul_le_mul_of_nonneg_left hfirst hs.le
  have hbound : |(∫ z, ψ (kernel n (a+s*y) (X z)) ∂μ)-α*(s*(∫ z, max (y-Z z) 0 ∂μ))| ≤
      s*(C*(4*s*(y^2+K)+|a-t| *(|y|+1+K))) := by
    apply hh.trans
    calc
      _ ≤ C*(4*(s^2*y^2+s^2*K)+|a-t| *(s*|y|+s*(1+K))) := by
        apply mul_le_mul_of_nonneg_left _ hC
        exact add_le_add (mul_le_mul_of_nonneg_left (add_le_add le_rfl hsecond) (by norm_num))
          (mul_le_mul_of_nonneg_left (add_le_add le_rfl hfirst') (abs_nonneg _))
      _ = _ := by ring
  have hd := (div_le_iff₀ hs).mpr (show
      |(∫ z, ψ (kernel n (a+s*y) (X z)) ∂μ)-α*(s*(∫ z, max (y-Z z) 0 ∂μ))| ≤
      (C*(4*s*(y^2+K)+|a-t| *(|y|+1+K)))*s by simpa only [mul_comm] using hbound)
  have he : ((∫ z, ψ (kernel n (a+s*y) (X z)) ∂μ)-
      α*(s*(∫ z, max (y-Z z) 0 ∂μ)))/s =
      (∫ z, ψ (kernel n (a+s*y) (X z)) ∂μ)/s-α*(∫ z, max (y-Z z) 0 ∂μ) := by
    field_simp
  rw [← he,abs_div,abs_of_pos hs]
  exact hd

end FCAppendix.PayOnce.KernelEntryExpectation
