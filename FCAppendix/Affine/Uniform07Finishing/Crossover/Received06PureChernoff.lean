import FCAppendix.PayOnce.Receipt
import FCAppendix.Finite.RankConcentration
import FCAppendix.Affine.Uniform07.SourceRateBounds
import FCAppendix.Affine.Uniform06.PureUnionUpper

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing.Crossover.Received06
open MeasureTheory Set Filter Topology
open Uniform06 Uniform07

theorem binomBelow_chernoff (N c : ℕ) (hc : c≤ N+1) {p θ : ℝ}
    (hp : p∈Icc (0:ℝ) 1) (hθ : θ≤ 0) :
    Bayes.binomBelow N p c≤ Real.exp (-θ*(c:ℝ))*(1-p+p*Real.exp θ)^N := by
  classical
  rw [Bayes.binomBelow_eq_prob N c hc p hp.1 hp.2]
  let μ:=IndependentCounts.binomial N p hp.1 hp.2
  have hpw (r : Fin (N+1)) : (if r.val< c then (1:ℝ) else 0)≤
      Real.exp (-θ*(c:ℝ))*(Real.exp θ)^r.val := by
    rw [←Real.exp_nat_mul,←Real.exp_add]
    by_cases hr : r.val< c
    · rw [if_pos hr]
      apply Real.one_le_exp
      have hrc : (r.val:ℝ)≤ c := by exact_mod_cast hr.le
      have hh:=mul_le_mul_of_nonpos_left hrc hθ
      nlinarith
    · rw [if_neg hr]
      exact (Real.exp_pos _).le
  have hh:=μ.expect_mono hpw
  rw [FiniteLaw.expect_const_mul,
    IndependentCounts.binomial_generating N p hp.1 hp.2 (Real.exp θ)] at hh
  simpa only [FiniteLaw.prob_eq_expect,μ] using! hh

theorem binaryOptimizer_negative {rho q : ℝ} (hrho : rho∈Ioo (0:ℝ) 1)
    (hq : q∈Ioo rho 1) : Ample.binaryOptimizer rho q<0 := by
  have hq0 : 0< q := hrho.1.trans hq.1
  unfold Ample.binaryOptimizer
  have hr : 0 < 1-rho := sub_pos.mpr hrho.2
  have hq1 : 0 < 1-q := sub_pos.mpr hq.2
  apply Real.log_neg (div_pos (mul_pos hrho.1 hq1) (mul_pos hq0 hr))
  apply (div_lt_one (mul_pos hq0 hr)).mpr
  nlinarith [hq.1]

def entryPureParameter (i : Row) : ℝ := pureParameter i (x i)
def entryPureTilt (i : Row) : ℝ := Ample.binaryOptimizer rho (entryPureParameter i)
def entryPureMGF (i : Row) : ℝ :=
  1-entryPureParameter i+entryPureParameter i*Real.exp (entryPureTilt i)
def entryPureCoefficient (i : Row) : ℝ := Real.exp (-Real.log (entryPureMGF i))

theorem entryPureParameter_mem (i : Row) : entryPureParameter i∈Ioo rho 1 := by
  have hx : (1/2:ℝ)≤ x i := by cases i <;> norm_num [x,xQ]
  have hp:=pure_parameter_range i ⟨hx,le_rfl⟩
  change pureParameter i (x i)∈Ioo rho 1
  exact ⟨hp.1,by linarith [hp.2]⟩

theorem entryPureTilt_negative (i : Row) : entryPureTilt i<0 :=
  binaryOptimizer_negative (by norm_num [rho]) (entryPureParameter_mem i)

theorem entryPureMGF_positive (i : Row) : 0< entryPureMGF i := by
  have hp:=entryPureParameter_mem i
  have h0 : 0< entryPureParameter i := by norm_num [rho] at hp; linarith [hp.1]
  unfold entryPureMGF
  exact add_pos (sub_pos.mpr hp.2) (mul_pos h0 (Real.exp_pos _))

theorem entryPureCoefficient_positive (i : Row) : 0< entryPureCoefficient i :=
  Real.exp_pos _

theorem entryPureRate_identity (i : Row) :
    rho*entryPureTilt i-Real.log (entryPureMGF i)=pureRate i (x i) := by
  have hp:=entryPureParameter_mem i
  have h0 : 0< entryPureParameter i := by norm_num [rho] at hp; linarith [hp.1]
  have hh:=Ample.binary_objective_optimizer h0 hp.2
    (show 0< rho by norm_num [rho]) (show rho<1 by norm_num [rho])
  simpa only [entryPureTilt,entryPureMGF,entryPureParameter,
    pureRate,Ample.binaryKL] using hh

theorem original_pure_rank_chernoff (i : Row) {m : ℕ} (hm : 1≤ m)
    {p : ℝ} (hp : p∈Icc (0:ℝ) 1) (hentry : entryPureParameter i≤ p) :
    Bayes.binomBelow (m-1) p (capacity m)≤
      entryPureCoefficient i*Real.exp (-pureRate i (x i)*(m:ℝ)) := by
  have hcap := (PhysicalRates.capacity_floor_bounds m).2
  have hcapN : capacity m≤ m-1+1 := by
    rw [Nat.sub_add_cancel hm]
    have hc : (capacity m:ℝ)≤ m := by
      norm_num only [rho] at hcap
      nlinarith [show (0:ℝ) ≤ m from Nat.cast_nonneg m]
    exact_mod_cast hc
  have hh:=binomBelow_chernoff (m-1) (capacity m) hcapN hp (entryPureTilt_negative i).le
  have hθ : Real.exp (entryPureTilt i)≤ 1 := Real.exp_le_one_iff.mpr (entryPureTilt_negative i).le
  have hmgf : 1-p+p*Real.exp (entryPureTilt i)≤ entryPureMGF i := by
    unfold entryPureMGF
    nlinarith [mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hentry)
      (sub_nonpos.mpr hθ)]
  have hmgf0 : 0≤ 1-p+p*Real.exp (entryPureTilt i) :=
    add_nonneg (sub_nonneg.mpr hp.2) (mul_nonneg hp.1 (Real.exp_pos _).le)
  have hpow:=pow_le_pow_left₀ hmgf0 hmgf (m-1)
  have h1:=hh.trans (mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le)
  have hpweq : (entryPureMGF i)^(m-1)=
      Real.exp (((m-1:ℕ):ℝ)*Real.log (entryPureMGF i)) := by
    rw [Real.exp_nat_mul,Real.exp_log (entryPureMGF_positive i)]
  rw [hpweq,←Real.exp_add] at h1
  have he : -entryPureTilt i*(capacity m:ℝ)+
      ((m-1:ℕ):ℝ)*Real.log (entryPureMGF i)≤
      -Real.log (entryPureMGF i)-pureRate i (x i)*(m:ℝ) := by
    rw [Nat.cast_sub hm,Nat.cast_one]
    have ht:=mul_le_mul_of_nonneg_left hcap (neg_nonneg.mpr (entryPureTilt_negative i).le)
    have hi:=entryPureRate_identity i
    nlinarith
  refine h1.trans ((Real.exp_le_exp.mpr he).trans_eq ?_)
  rw [entryPureCoefficient,←Real.exp_add]
  congr 1
  ring

end FCAppendix.Affine.Uniform07Finishing.Crossover.Received06
