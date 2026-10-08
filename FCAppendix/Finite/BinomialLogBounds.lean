import FCAppendix.Finite.PPITailArea
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

noncomputable section
namespace FCAppendix.Bayes
open Set
open scoped BigOperators

private theorem hasDerivAt_pow_score (r : ℕ) (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt (fun p : ℝ => p ^ r) (x ^ r * ((r : ℝ) / x)) x := by
  have hh := hasDerivAt_pow r x
  apply hh.congr_deriv
  cases r with
  | zero => simp
  | succ r => simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, pow_succ]
              field_simp

theorem hasDerivAt_binomial_mass_score (N r : ℕ) (hr : r ≤ N) (p : ℝ)
    (hp : p ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun a => PiBinomial.pmf N a r)
      (PiBinomial.pmf N p r * (((r : ℝ) - N * p) / (p * (1 - p)))) p := by
  have h1 := hasDerivAt_pow_score r p hp.1.ne'
  have h2 := (hasDerivAt_pow_score (N-r) (1-p) (sub_pos.mpr hp.2).ne').comp p
    ((hasDerivAt_id p).const_sub 1)
  have hh := (h1.mul h2).const_mul (N.choose r : ℝ)
  simp only [Pi.mul_apply, Function.comp_def] at hh
  have he : (N.choose r : ℝ) *
      (p ^ r * ((r:ℝ)/p) * (1-p)^(N-r) +
       p^r * ((1-p)^(N-r) * ((N-r:ℕ)/(1-p)) * -1)) =
      PiBinomial.pmf N p r * (((r:ℝ)-N*p)/(p*(1-p))) := by
    unfold PiBinomial.pmf
    rw [Nat.cast_sub hr]
    field_simp [hp.1.ne', (sub_pos.mpr hp.2).ne']
    ring
  simpa only [PiBinomial.pmf, mul_assoc] using hh.congr_deriv he

theorem binomBelow_pos (N c : ℕ) (hc : 0 < c) (p : ℝ)
    (hp : p ∈ Ioo (0 : ℝ) 1) : 0 < binomBelow N p c := by
  unfold binomBelow
  apply Finset.sum_pos'
  · intro r _
    unfold PiBinomial.pmf
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hp.1.le _)) (pow_nonneg (sub_pos.mpr hp.2).le _)
  · refine ⟨0, Finset.mem_range.mpr hc, ?_⟩
    simpa [PiBinomial.pmf] using pow_pos (sub_pos.mpr hp.2) N

theorem hasDerivAt_log_binomBelow (N c : ℕ) (hc : 0 < c) (hcN : c ≤ N+1)
    (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun a => Real.log (binomBelow N a c))
      ((∑ r ∈ Finset.range c, PiBinomial.pmf N p r *
        (((r : ℝ) - N*p)/(p*(1-p)))) / binomBelow N p c) p := by
  have hh : HasDerivAt (fun a => binomBelow N a c)
      (∑ r ∈ Finset.range c, PiBinomial.pmf N p r *
        (((r : ℝ) - N*p)/(p*(1-p)))) p := by
    simpa only [binomBelow, Finset.sum_apply] using
      HasDerivAt.fun_sum (u := Finset.range c) (fun r hr =>
        hasDerivAt_binomial_mass_score N r (by have := Finset.mem_range.mp hr; omega) p hp)
  exact hh.log (binomBelow_pos N c hc p hp).ne'

theorem log_binomBelow_deriv_bounds (N c : ℕ) (hc : 0 < c) (hcN : c ≤ N+1)
    (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) :
    -(N : ℝ)/(1-p) ≤ deriv (fun a => Real.log (binomBelow N a c)) p ∧
    deriv (fun a => Real.log (binomBelow N a c)) p ≤
      -((N : ℝ)*p-(c-1 : ℕ))/(p*(1-p)) := by
  rw [(hasDerivAt_log_binomBelow N c hc hcN p hp).deriv]
  have hden : 0 < p*(1-p) := mul_pos hp.1 (sub_pos.mpr hp.2)
  have hQ := binomBelow_pos N c hc p hp
  have hmass (r : ℕ) : 0 ≤ PiBinomial.pmf N p r := by
    unfold PiBinomial.pmf
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hp.1.le _)) (pow_nonneg (sub_pos.mpr hp.2).le _)
  constructor
  · apply (le_div_iff₀ hQ).mpr
    rw [binomBelow, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro r hr
    have hscore : -(N : ℝ)/(1-p) ≤ ((r : ℝ)-N*p)/(p*(1-p)) := by
      apply (le_div_iff₀ hden).mpr
      have he : -(N : ℝ)/(1-p)*(p*(1-p)) = -(N:ℝ)*p := by field_simp [(sub_pos.mpr hp.2).ne']
      rw [he]
      have := (Nat.cast_nonneg r : (0:ℝ) ≤ r)
      linarith
    simpa only [mul_comm (-(N:ℝ)/(1-p))] using mul_le_mul_of_nonneg_left hscore (hmass r)
  · apply (div_le_iff₀ hQ).mpr
    rw [binomBelow, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro r hr
    have hrN : (r : ℝ) ≤ (c-1 : ℕ) := by exact_mod_cast (show r ≤ c-1 by have := Finset.mem_range.mp hr; omega)
    have hs : ((r : ℝ)-N*p)/(p*(1-p)) ≤ -((N:ℝ)*p-(c-1:ℕ))/(p*(1-p)) :=
      div_le_div_of_nonneg_right (by linarith) hden.le
    simpa only [mul_comm (-((N:ℝ)*p-(c-1:ℕ))/(p*(1-p)))] using
      mul_le_mul_of_nonneg_left hs (hmass r)

theorem log_binomBelow_sub_le (N c : ℕ) (hc : 0 < c) (hcN : c ≤ N+1)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) :
    Real.log (binomBelow N a c) - Real.log (binomBelow N b c) ≤
      (N : ℝ) / (1-b) * (b-a) := by
  have hmem (x : ℝ) (hx : x ∈ Icc a b) : x ∈ Ioo (0:ℝ) 1 :=
    ⟨ha.trans_le hx.1, hx.2.trans_lt hb⟩
  have hcont : ContinuousOn (fun x => Real.log (binomBelow N x c)) (Icc a b) := by
    intro x hx
    exact (hasDerivAt_log_binomBelow N c hc hcN x (hmem x hx)).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ (fun x => Real.log (binomBelow N x c)) (interior (Icc a b)) := by
    intro x hx
    exact (hasDerivAt_log_binomBelow N c hc hcN x
      (hmem x (interior_subset hx))).differentiableAt.differentiableWithinAt
  have hder (x : ℝ) (hx : x ∈ interior (Icc a b)) :
      -(N:ℝ)/(1-b) ≤ deriv (fun x => Real.log (binomBelow N x c)) x := by
    have hx' := interior_subset hx
    have hh := (log_binomBelow_deriv_bounds N c hc hcN x (hmem x hx')).1
    have hm := div_le_div_of_nonneg_left (Nat.cast_nonneg N) (sub_pos.mpr hb)
      (show 1-b ≤ 1-x by linarith [hx'.2])
    have he : -(N:ℝ)/(1-b) ≤ -(N:ℝ)/(1-x) := by simpa only [neg_div] using neg_le_neg hm
    exact he.trans hh
  have hh := (convex_Icc a b).mul_sub_le_image_sub_of_le_deriv hcont hdiff hder
    a ⟨le_rfl,hab⟩ b ⟨hab,le_rfl⟩ hab
  simp only [neg_div, neg_mul] at hh
  linarith

theorem binomBelow_le_exp_mul_of_rank_gap (N c : ℕ) (hc : 0 < c) (hcN : c ≤ N+1)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (hb : b < 1)
    (hgap : 0 ≤ (N:ℝ)*a-(c-1:ℕ)) :
    binomBelow N b c ≤ Real.exp (-((N:ℝ)*a-(c-1:ℕ))*(b-a)) * binomBelow N a c := by
  have hmem (x : ℝ) (hx : x ∈ Icc a b) : x ∈ Ioo (0:ℝ) 1 :=
    ⟨ha.trans_le hx.1, hx.2.trans_lt hb⟩
  have hcont : ContinuousOn (fun x => Real.log (binomBelow N x c)) (Icc a b) := by
    intro x hx
    exact (hasDerivAt_log_binomBelow N c hc hcN x (hmem x hx)).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ (fun x => Real.log (binomBelow N x c)) (interior (Icc a b)) := by
    intro x hx
    exact (hasDerivAt_log_binomBelow N c hc hcN x
      (hmem x (interior_subset hx))).differentiableAt.differentiableWithinAt
  have hder (x : ℝ) (hx : x ∈ interior (Icc a b)) :
      deriv (fun x => Real.log (binomBelow N x c)) x ≤ -((N:ℝ)*a-(c-1:ℕ)) := by
    have hx' := interior_subset hx
    have hp := hmem x hx'
    have hh := (log_binomBelow_deriv_bounds N c hc hcN x hp).2
    have hnum : (N:ℝ)*a-(c-1:ℕ) ≤ (N:ℝ)*x-(c-1:ℕ) := by
      nlinarith [mul_le_mul_of_nonneg_left hx'.1 (Nat.cast_nonneg N)]
    have hden : 0 < x*(1-x) := mul_pos hp.1 (sub_pos.mpr hp.2)
    have hden1 : x*(1-x) ≤ 1 := by nlinarith [sq_nonneg x]
    have hl : (N:ℝ)*a-(c-1:ℕ) ≤ ((N:ℝ)*x-(c-1:ℕ))/(x*(1-x)) := by
      apply (le_div_iff₀ hden).mpr
      exact (mul_le_of_le_one_right hgap hden1).trans hnum
    rw [neg_div] at hh
    linarith
  have hh := (convex_Icc a b).image_sub_le_mul_sub_of_deriv_le hcont hdiff hder
    a ⟨le_rfl,hab⟩ b ⟨hab,le_rfl⟩ hab
  have hexp := Real.exp_le_exp.mpr (show Real.log (binomBelow N b c) ≤
      -((N:ℝ)*a-(c-1:ℕ))*(b-a) + Real.log (binomBelow N a c) by linarith)
  rwa [Real.exp_add, Real.exp_log (binomBelow_pos N c hc a ⟨ha,hab.trans_lt hb⟩),
    Real.exp_log (binomBelow_pos N c hc b ⟨ha.trans_le hab,hb⟩)] at hexp

end FCAppendix.Bayes
