import FCAppendix.Affine.Uniform07.ParameterCertificate
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import FCAppendix.Affine.Uniform07.ExactIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace FCAppendix.Affine.Uniform07
open MeasureTheory Set Filter Topology

noncomputable def activeMarginal (lambda v : ℝ) : ℝ := 1-lambda/v

theorem active_marginal_integral {lambda t : ℝ} (hl : 0<lambda) (hlt : lambda≤t) :
    (∫ v in lambda..t,activeMarginal lambda v)=
      t-lambda+lambda*(Real.log lambda-Real.log t) := by
  calc
    _ = moment 1 lambda lambda t 1 := by simpa only [activeMarginal, pow_one] using integral_moment 1 lambda 1 hl hlt
    _ = _ := by
      norm_num [moment, Finset.sum_range_succ, invMoment]
      ring

theorem active_duplicate_integral {lambda t : ℝ} (hl : 0<lambda) (hlt : lambda≤t) :
    (∫ v in lambda..t,(activeMarginal lambda v)^2)=
      t-lambda^2/t+2*lambda*(Real.log lambda-Real.log t) := by
  calc
    _ = moment 1 lambda lambda t 2 := integral_moment 1 lambda 2 hl hlt
    _ = _ := by
      norm_num [moment, Finset.sum_range_succ, invMoment]
      field_simp [hl.ne', (hl.trans_le hlt).ne']
      ring

theorem source_profile_integrals (i : Row) :
    (∫ v in entry i..cutoff i,(activeMarginal (entry i) v)^2)=limitDup i ∧
    1-cutoff i+2*(∫ v in entry i..cutoff i,activeMarginal (entry i) v)=1-delta := by
  have ht := cutoff_pos i
  have hx : x i∈Ioo 0 1 := by cases i <;> norm_num [x,xQ]
  have hl : 0<entry i := mul_pos hx.1 ht
  have hlt : entry i≤cutoff i := by unfold entry; nlinarith [hx.2]
  have hlog : Real.log (entry i)-Real.log (cutoff i)=Real.log (x i) := by
    rw [entry,Real.log_mul hx.1.ne' ht.ne']; ring
  have hcut := cutoff_equation i (cutoff_den_ne i)
  constructor
  · rw [active_duplicate_integral hl hlt,hlog]
    unfold limitDup entry
    field_simp
  · rw [active_marginal_integral hl hlt,hlog]
    unfold entry at *
    nlinarith

theorem binomial_pair_outcomes {p : ℝ} (hp : p∈Ioc 0 1) :
    0<2*p-p^2 ∧ (2*p)/(2*p-p^2)=2/(2-p) ∧
    2*p-(2*p-p^2)=p^2 := by
  have h2 : 0<2-p := by linarith [hp.2]
  have hs : 0<2*p-p^2 := by nlinarith [mul_pos hp.1 h2]
  refine ⟨hs,?_,by ring⟩
  field_simp [hp.1.ne', h2.ne']

theorem conditional_product_error {p p1 p2 : ℝ}
    (hp : p∈Icc 0 1) (_h1 : p1∈Icc 0 1) (h2 : p2∈Icc 0 1) :
    |p1*p2-p^2|≤|p1-p|+|p2-p| := by
  calc
    _ = |(p1-p)*p2+p*(p2-p)| := by congr 1; ring
    _ ≤ |(p1-p)*p2|+|p*(p2-p)| := abs_add_le _ _
    _ ≤ |p1-p|+|p2-p| := by
      rw [abs_mul,abs_mul,abs_of_nonneg h2.1,abs_of_nonneg hp.1]
      nlinarith [mul_le_mul_of_nonneg_left h2.2 (abs_nonneg (p1-p)),
        mul_le_mul_of_nonneg_right hp.2 (abs_nonneg (p2-p))]

theorem bounded_count_integral_limit {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsFiniteMeasure mu] (f : ℕ→Ω→ℝ) (g : Ω→ℝ)
    (hmeas : ∀ n,AEStronglyMeasurable (f n) mu)
    (hbound : ∀ n,∀ᵐ v∂mu,|f n v|≤2)
    (hlim : ∀ᵐ v∂mu,Tendsto (fun n => f n v) atTop (𝓝 (g v))) :
    Tendsto (fun n => ∫ v,f n v∂mu) atTop (𝓝 (∫ v,g v∂mu)) := by
  apply tendsto_integral_of_dominated_convergence (fun _ => (2:ℝ)) hmeas (integrable_const 2)
  · intro n; filter_upwards [hbound n] with v hv; simpa [Real.norm_eq_abs] using hv
  · exact hlim

theorem ae_limit_of_finite_exceptions {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) [NullSingletonClass mu] {f : ℕ→Ω→ℝ} {g : Ω→ℝ}
    (E : Finset Ω)
    (h : ∀ v∉(E:Set Ω),Tendsto (fun n => f n v) atTop (𝓝 (g v))) :
    ∀ᵐ v∂mu,Tendsto (fun n => f n v) atTop (𝓝 (g v)) := by
  have hnull : mu (E:Set Ω)=0 := E.finite_toSet.measure_zero mu
  have hae : ∀ᵐ v∂mu,v∉(E:Set Ω) := by
    rw [ae_iff]
    simpa using hnull
  filter_upwards [hae] with v hv
  exact h v hv

theorem common_finite_comparisons {D1 D2 Q1 Q2 : ℕ→ℝ}
    {d1 d2 q1 q2 : ℝ}
    (hD1 : Tendsto D1 atTop (𝓝 d1)) (hD2 : Tendsto D2 atTop (𝓝 d2))
    (hQ1 : Tendsto Q1 atTop (𝓝 q1)) (hQ2 : Tendsto Q2 atTop (𝓝 q2))
    (hd : d1<d2) (hq : q2<q1) :
    ∃ N,∀ m≥N,D1 m<D2 m ∧ Q2 m<Q1 m := by
  have h1 : ∀ᶠ m in atTop,D1 m<D2 m := Filter.Tendsto.eventually_lt hD1 hD2 hd
  have h2 : ∀ᶠ m in atTop,Q2 m<Q1 m := Filter.Tendsto.eventually_lt hQ2 hQ1 hq
  exact Filter.eventually_atTop.mp (h1.and h2)

end FCAppendix.Affine.Uniform07
