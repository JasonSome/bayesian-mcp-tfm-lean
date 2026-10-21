import FCAppendix.Affine.Uniform07Finishing.Crossover.Received06PureUnionLower
import FCAppendix.Affine.Uniform07Finishing.Crossover.Received06DuplicateDerivative
import FCAppendix.Affine.Uniform07Finishing.Crossover.Received06PureHazard
import FCAppendix.Affine.Uniform07Finishing.Crossover.Received06Low

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing.Crossover.Received06
open MeasureTheory ProbabilityTheory Set Filter Topology Classical Uniform06 Physical

def pureValueRate (row : Uniform07.Row) : ℝ:=
  Classical.choose (eventually_source_pure_union_relative row)

theorem pureValueRate_pos (row : Uniform07.Row) : 0< pureValueRate row:=
  (Classical.choose_spec (eventually_source_pure_union_relative row)).1

def pureDerivativeRate (row : Uniform07.Row) : ℝ:=
  Classical.choose (SharpPureDerivative.eventually_source_derivative_bounds row)

theorem pureDerivativeRate_pos (row : Uniform07.Row) : 0< pureDerivativeRate row:=
  (Classical.choose_spec (SharpPureDerivative.eventually_source_derivative_bounds row)).1

def pureValueError (row : Uniform07.Row) (m : ℕ) : ℝ:=
  2*Real.exp (-pureValueRate row*(m:ℝ))+Real.exp (-(6/1000000:ℝ)*(m:ℝ))

def receivedSuccessError (row : Uniform07.Row) (m : ℕ) : ℝ:=
  pureValueError row m+2*SharpPureDerivative.relativeError (pureDerivativeRate row) m

def receivedDuplicateError (row : Uniform07.Row) (m : ℕ) : ℝ:=
  (lowRankConstant row+40001)*(m:ℝ)*Real.exp (-(6/1000000:ℝ)*(m:ℝ))

theorem receivedSuccessError_nonnegative (row : Uniform07.Row) (m : ℕ) :
    0≤ receivedSuccessError row m := by
  unfold receivedSuccessError pureValueError SharpPureDerivative.relativeError
  positivity

theorem receivedDuplicateError_nonnegative (row : Uniform07.Row) (m : ℕ) :
    0≤ receivedDuplicateError row m := by
  have hK:=lowRankConstant_nonnegative row
  unfold receivedDuplicateError
  positivity

theorem pureValueError_le_received (row : Uniform07.Row) (m : ℕ) :
    pureValueError row m≤ receivedSuccessError row m := by
  unfold receivedSuccessError SharpPureDerivative.relativeError
  exact le_add_of_nonneg_right (by positivity)

theorem pureDerivativeError_le_received (row : Uniform07.Row) (m : ℕ) :
    2*SharpPureDerivative.relativeError (pureDerivativeRate row) m≤ receivedSuccessError row m := by
  unfold receivedSuccessError pureValueError
  exact le_add_of_nonneg_left (by positivity)

def receivedSuccessRate (row : Uniform07.Row) : ℝ:=
  min (pureValueRate row) (min (pureDerivativeRate row) (6/1000000))

def receivedSuccessCoefficient : ℝ:=3+2*Real.exp 1+20000*Real.exp (1/10)

theorem receivedSuccessRate_pos (row : Uniform07.Row) : 0< receivedSuccessRate row :=
  lt_min (pureValueRate_pos row) (lt_min (pureDerivativeRate_pos row) (by norm_num))

theorem receivedSuccessError_chernoff (row : Uniform07.Row) (m : ℕ) :
    receivedSuccessError row m≤ receivedSuccessCoefficient*
      Real.exp (-receivedSuccessRate row*(m:ℝ)) := by
  have hm : (0:ℝ)≤ m:=Nat.cast_nonneg m
  have hv : receivedSuccessRate row≤ pureValueRate row:=min_le_left _ _
  have hd : receivedSuccessRate row≤ pureDerivativeRate row:=
    (min_le_right _ _).trans (min_le_left _ _)
  have hs : receivedSuccessRate row≤(6/1000000:ℝ):=
    (min_le_right _ _).trans (min_le_right _ _)
  have hv':=Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_right hv hm))
  have hd':=Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_right hd hm))
  have hs':=Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_right hs hm))
  have h₁:=mul_le_mul_of_nonneg_left hv' (by norm_num : (0:ℝ)≤ 2)
  have h₂:=mul_le_mul_of_nonneg_left hd' (show 0≤ 2*Real.exp 1 by positivity)
  have h₃:=mul_le_mul_of_nonneg_left hs' (show 0≤ 20000*Real.exp (1/10) by positivity)
  unfold receivedSuccessError pureValueError SharpPureDerivative.relativeError receivedSuccessCoefficient
  rw [show Real.exp (1-pureDerivativeRate row*m)=
      Real.exp 1*Real.exp (-pureDerivativeRate row*m) by rw [←Real.exp_add]; congr 1; ring,
    show Real.exp (1/10-(6/1000000:ℝ)*m)=
      Real.exp (1/10)*Real.exp (-(6/1000000:ℝ)*m) by rw [←Real.exp_add]; congr 1; ring]
  simp only [neg_mul] at h₁ h₂ h₃ hs' ⊢
  nlinarith only [h₁,h₂,h₃,hs',Real.exp_pos (-receivedSuccessRate row*(m:ℝ))]

theorem receivedDuplicateError_tendsto (row : Uniform07.Row) :
    Tendsto (receivedDuplicateError row) atTop (𝓝 0) := by
  have hh : Tendsto (fun m : ℕ=>(m:ℝ)*Real.exp (-(6/1000000:ℝ)*(m:ℝ))) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Real.rpow_one] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1:ℝ) (6/1000000) (by norm_num)).comp
        tendsto_natCast_atTop_atTop
  change Tendsto (fun m : ℕ => (lowRankConstant row+40001)*(m:ℝ)*
    Real.exp (-(6/1000000:ℝ)*(m:ℝ))) atTop (𝓝 0)
  simpa only [mul_assoc,mul_zero] using
    hh.const_mul (lowRankConstant row+40001)

theorem receivedDuplicateError_rent_identity (row : Uniform07.Row) {m : ℕ} (hm : 0< m) :
    receivedDuplicateError row m/((m:ℝ)*sourceCrossoverStart row*lowBenchmark m/2)=
      (4*(lowRankConstant row+40001)/sourceCrossoverStart row)*
        Real.exp (-(3/1000000:ℝ)*(m:ℝ)) := by
  have hm0 : (m:ℝ)≠0:=(Nat.cast_pos.mpr hm).ne'
  have hL:=(source_crossover_geometry row).1.ne'
  have hE:=Real.exp_ne_zero (-(3/1000000:ℝ)*(m:ℝ))
  have hs : Real.exp (-(6/1000000:ℝ)*(m:ℝ))=
      Real.exp (-(3/1000000:ℝ)*(m:ℝ))*Real.exp (-(3/1000000:ℝ)*(m:ℝ)) := by
    rw [←Real.exp_add]
    congr 1
    ring
  unfold receivedDuplicateError lowBenchmark
  rw [hs]
  field_simp [hm0,hL,hE]
  ring

theorem receivedDuplicateError_rent_tendsto (row : Uniform07.Row) :
    Tendsto (fun m=>receivedDuplicateError row m/
      ((m:ℝ)*sourceCrossoverStart row*lowBenchmark m/2)) atTop (𝓝 0) := by
  have hh:=LiteralWeakRent.tendsto_exp_affine_nat (by norm_num : (0:ℝ)<3/1000000) 0
  have ht:=hh.const_mul (4*(lowRankConstant row+40001)/sourceCrossoverStart row)
  have hswap (m : ℕ) : -(3/1000000:ℝ)*(m:ℝ)=-(m:ℝ)*(3/1000000) := by ring
  apply (show Tendsto
    (fun m : ℕ=>(4*(lowRankConstant row+40001)/sourceCrossoverStart row)*
      Real.exp (-(3/1000000:ℝ)*(m:ℝ))) atTop (𝓝 0) by
        simpa only [zero_sub,←neg_mul,mul_zero,hswap] using ht).congr'
  filter_upwards [eventually_gt_atTop (0:ℕ)] with m hm
  exact (receivedDuplicateError_rent_identity row hm).symm

theorem normalize_pure_duplicate {m K E r Q q P M' D D' : ℝ}
    (hm : 0< m) (hK : 0≤ K) (hE : 0< E) (hr : 0≤ r)
    (hQ : E≤ Q) (hQq : Q≤ q) (hP : m/40000*E≤ P) (hM : 0≤ M')
    (hD : D∈Icc (0:ℝ) (r*E))
    (hD' : D'∈Icc (0:ℝ) (m*(r*E)*(M'+K))) :
    |D|≤((K+40001)*m*r)*q/m ∧
    |D'|≤((K+40001)*m*r)*((P*M')/m+q) := by
  have hq : 0≤ q:=hE.le.trans (hQ.trans hQq)
  have hqE:=hQ.trans hQq
  have hflow : 0≤ P*M':=mul_nonneg ((by positivity : 0≤ m/40000*E).trans hP) hM
  have hscale : 0≤ K+40001:=by linarith
  have hB : r*E≤(K+40001)*r*q := by
    have hh:=mul_le_mul_of_nonneg_left hqE hr
    have hh':=mul_le_mul_of_nonneg_right (show (1:ℝ)≤ K+40001 by linarith) (mul_nonneg hr hq)
    nlinarith only [hh,hh']
  refine ⟨?_,?_⟩
  · rw [abs_of_nonneg hD.1]
    have he : ((K+40001)*m*r)*q/m=(K+40001)*r*q:=by field_simp [hm.ne']
    rw [he]
    exact hD.2.trans hB
  · rw [abs_of_nonneg hD'.1]
    have hp:=mul_le_mul_of_nonneg_right hP (mul_nonneg hr hM)
    have hf:=mul_le_mul_of_nonneg_right (show (40000:ℝ)≤ K+40001 by linarith)
      (mul_nonneg hr hflow)
    have he:=mul_le_mul_of_nonneg_left hqE (mul_nonneg (mul_nonneg hm.le hr) hK)
    have he':=mul_le_mul_of_nonneg_right (show K≤ K+40001 by linarith)
      (mul_nonneg (mul_nonneg hm.le hr) hq)
    have hid : ((K+40001)*m*r)*((P*M')/m+q)=
        (K+40001)*r*(P*M')+(K+40001)*m*r*q:=by field_simp [hm.ne']
    rw [hid]
    nlinarith only [hD'.2,hp,hf,he,he']

end FCAppendix.Affine.Uniform07Finishing.Crossover.Received06
