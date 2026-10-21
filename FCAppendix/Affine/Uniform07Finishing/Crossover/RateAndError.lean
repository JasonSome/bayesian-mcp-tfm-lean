import FCAppendix.Affine.Uniform07Finishing.Crossover.Boundary
import FCAppendix.Affine.Uniform07.RateSeparation

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing.Crossover
open Set Filter Topology MeasureTheory

theorem finite_physical_rate_separation (i : Uniform07.Row)
    {m a p p' : ℝ} (hm : 0< m) (hp : 0< p)
    (hcanonical : (Uniform07.slopeRatioLower i/500-1/10000)*m≤ a)
    (hpure : p'≤(21/10000:ℝ)*m*p) :
    (1+1/4:ℝ)*p'< a*p := by
  have hchecked : (16211/10000:ℝ)< Uniform07.slopeRatioLower i := by
    cases i with
    | first => exact Uniform07.physical_slope_numerics.1
    | second => linarith [Uniform07.physical_slope_numerics.2]
  have hscalar : (1+1/4:ℝ)*(21/10000) <
      Uniform07.slopeRatioLower i/500-1/10000 := by linarith
  have hmp : 0< m*p := mul_pos hm hp
  have hstrict := mul_lt_mul_of_pos_right hscalar hmp
  have hc := mul_le_mul_of_nonneg_right hcanonical hp.le
  have hp' := mul_le_mul_of_nonneg_left hpure (by norm_num : (0:ℝ)≤ 1+1/4)
  nlinarith

theorem normalized_barrier_residual
    (eta b alpha A r s s0 lead m : ℝ)
    (hmatch : 2*A*lead=2+eta*b*s0) :
    (2-(1-eta)*r+eta*b*s)-lead*(2*alpha-s/m) =
      -(1-eta)*r+eta*b*(s-s0)-2*lead*(alpha-A)+lead*s/m := by
  linear_combination -hmatch

theorem normalized_barrier_residual_bound
    {eta b alpha A r s s0 lead m ea er es Lmax Smax : ℝ}
    (hm : 0< m) (_hea : 0≤ ea) (_her : 0≤ er) (_hes : 0≤ es)
    (hLmax : 0≤ Lmax) (_hSmax : 0≤ Smax)
    (hmatch : 2*A*lead=2+eta*b*s0)
    (ha : |alpha-A|≤ ea) (hr : |r|≤ er) (hs : |s-s0|≤ es)
    (hlead : |lead|≤ Lmax) (hsBound : |s|≤ Smax) :
    |(2-(1-eta)*r+eta*b*s)-lead*(2*alpha-s/m)| ≤
    |1-eta| * er+|eta*b| * es+2*Lmax*ea+Lmax*Smax/m := by
  rw [normalized_barrier_residual eta b alpha A r s s0 lead m hmatch]
  have h₁ : |-(1-eta)*r|≤|1-eta| * er := by
    rw [abs_mul,abs_neg]
    exact mul_le_mul_of_nonneg_left hr (abs_nonneg _)
  have h₂ : |eta*b*(s-s0)|≤|eta*b| * es := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hs (abs_nonneg _)
  have h₃ : |2*lead*(alpha-A)|≤ 2*Lmax*ea := by
    rw [abs_mul,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤ 2)]
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left hlead (by norm_num)) ha (abs_nonneg _) (by positivity)
  have h₄ : |lead*s/m|≤ Lmax*Smax/m := by
    rw [abs_div,abs_mul,abs_of_pos hm]
    exact div_le_div_of_nonneg_right
      (mul_le_mul hlead hsBound (abs_nonneg _) hLmax) hm.le
  have ht₁ := abs_add_le (-(1-eta)*r) (eta*b*(s-s0))
  have ht₂ := abs_sub (-(1-eta)*r+eta*b*(s-s0)) (2*lead*(alpha-A))
  have ht₃ := abs_add_le (-(1-eta)*r+eta*b*(s-s0)-2*lead*(alpha-A)) (lead*s/m)
  nlinarith [h₁,h₂,h₃,h₄,ht₁,ht₂,ht₃]

theorem normalized_quotient_error
    {N K lead bound lower : ℝ}
    (hlower : 0< lower) (hK : lower≤ K)
    (hbound : 0≤ bound) (hres : |N-lead*K|≤ bound) :
    |N/K-lead|≤ bound/lower := by
  have hKpos : 0< K := hlower.trans_le hK
  have hid : N/K-lead=(N-lead*K)/K := by
    field_simp [hKpos.ne']
  rw [hid,abs_div,abs_of_pos hKpos]
  exact (div_le_div_of_nonneg_right hres hKpos.le).trans
    (div_le_div_of_nonneg_left hbound hlower hK)

theorem source_leading_match {eta xi b A x : ℝ}
    (hxi : xi≠0) (hb : b≠0) (hA : A≠0) :
    2*A*((1+(eta/xi)*x)/A)=2+eta*b*(2*x/(xi*b)) := by
  field_simp [hxi,hb,hA]

theorem source_eventual_strict_route_gap (i : Uniform07.Row)
    {v b q d a rentErr dupBudget : ℕ→ℝ}
    (hrentErr : Tendsto rentErr atTop (𝓝 0))
    (hdupBudget : Tendsto dupBudget atTop (𝓝 (2*Uniform07.eta i/Uniform07.xi i)))
    (hdupRatio : Tendsto (fun m => d m/q m) atTop (𝓝 0))
    (hfinite : ∀ᶠ m in atTop,
      0< a m ∧ 0< q m ∧ 0≤ d m ∧ d m≤ q m ∧ rentErr m≤ 1 ∧
      (1-rentErr m)/a m≤ v m-b m ∧
      Uniform07.eta i*b m*d m≤ dupBudget m*q m/a m) :
    ∀ᶠ m in atTop,
      utilityOne (v m) (b m) (q m)<
        utilityTwo (Uniform07.eta i) (v m) (b m) (q m) (d m) := by
  have hlimit : 2*Uniform07.eta i/Uniform07.xi i<1 := by
    linarith [Uniform07.route_coefficient_pos i]
  exact eventually_strict_route_gap hlimit hrentErr hdupBudget hdupRatio hfinite

end FCAppendix.Affine.Uniform07Finishing.Crossover
