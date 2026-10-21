import FCAppendix.Affine.Uniform07Finishing.Crossover.PhysicalGaps

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing.Crossover
open MeasureTheory ProbabilityTheory Bayes Game Set Filter Topology

namespace Physical
variable {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem actual_bid_le_value_of_zero_bid_IC (Γ : FiniteGame m 2 c Seed)
    (i : Fin m) {eta w b : ℝ} (heta : eta∈Icc (0:ℝ) 1)
    (hA : Γ.A=Schedule.affine 2 eta heta.1 heta.2) (hg : Γ.g=0)
    (hw : 0≤ w) (hb : 0≤ b) (hSpos : 0< success Γ i b)
    (hIC : (problem Γ i).payoff w (two 0)≤(problem Γ i).payoff w (two b)) :
    b≤ w := by
  have hz : 0≤(problem Γ i).payoff w (two 0) := by
    rw [LowBody.native_affine_zero_fee_payoff Γ heta.1 heta.2 hA hg]
    simp only [two_bid (le_refl (0:ℝ)),mul_zero,zero_mul,sub_zero]
    exact mul_nonneg hw (((problem Γ i).outcome (two 0)).success_nonneg)
  have hnonneg := hz.trans hIC
  rw [LowBody.native_affine_zero_fee_payoff Γ heta.1 heta.2 hA hg] at hnonneg
  simp only [two_bid hb] at hnonneg
  change 0≤(w-b)*success Γ i b-eta*b*duplicate Γ i b at hnonneg
  by_contra h
  have hwb : w-b<0 := sub_neg.mpr (lt_of_not_ge h)
  have hbad := mul_neg_of_neg_of_pos hwb hSpos
  have hdup : 0≤ eta*b*duplicate Γ i b :=
    mul_nonneg (mul_nonneg heta.1 hb) (duplicate_nonneg Γ i b)
  linarith

theorem half_value_broadcast_payoff_lower (Γ : FiniteGame m 2 c Seed)
    (i : Fin m) {eta w ell : ℝ} (heta : eta∈Icc (0:ℝ) 1)
    (hA : Γ.A=Schedule.affine 2 eta heta.1 heta.2) (hg : Γ.g=0)
    (hw : 0≤ w) (_hell : 0≤ ell)
    (hq : ell≤ q Γ i (w/2)) (hD : duplicate Γ i (w/2)≤ ell/2) :
    w*ell/2≤(problem Γ i).payoff w (two (w/2)) := by
  rw [two_payoff Γ heta.1 heta.2 hA hg i w (by positivity : 0≤ w/2)]
  unfold utilityTwo
  have hd0 := duplicate_nonneg Γ i (w/2)
  have hηd : eta*duplicate Γ i (w/2)≤ duplicate Γ i (w/2) :=
    mul_le_of_le_one_left hd0 heta.2
  have hmain : ell≤ 2*q Γ i (w/2)-(1+eta)*duplicate Γ i (w/2) := by nlinarith
  have hscaled := mul_le_mul_of_nonneg_left hmain (by positivity : 0≤ w/2)
  nlinarith

theorem actual_rent_lower_of_half_value_IC (Γ : FiniteGame m 2 c Seed)
    (i : Fin m) {eta w b ell : ℝ} (heta : eta∈Icc (0:ℝ) 1)
    (hA : Γ.A=Schedule.affine 2 eta heta.1 heta.2) (hg : Γ.g=0)
    (hw : 0≤ w) (hb : 0≤ b) (hell : 0< ell)
    (hq : ell≤ q Γ i (w/2)) (hDhalf : duplicate Γ i (w/2)≤ ell/2)
    (hSpos : 0< success Γ i b)
    (hIC : (problem Γ i).payoff w (two (w/2))≤(problem Γ i).payoff w (two b)) :
    b*ell/2≤ w-b ∧ b≤ w := by
  have hhalf := half_value_broadcast_payoff_lower Γ i heta hA hg hw hell.le hq hDhalf
  have htotal : w*ell/2≤(problem Γ i).payoff w (two b) := hhalf.trans hIC
  rw [LowBody.native_affine_zero_fee_payoff Γ heta.1 heta.2 hA hg] at htotal
  simp only [two_bid hb] at htotal
  change w*ell/2≤(w-b)*success Γ i b-eta*b*duplicate Γ i b at htotal
  have hdup : 0≤ eta*b*duplicate Γ i b :=
    mul_nonneg (mul_nonneg heta.1 hb) (duplicate_nonneg Γ i b)
  have hδ : 0≤ w-b := by
    by_contra hh
    have hneg : (w-b)*success Γ i b<0 := mul_neg_of_neg_of_pos (lt_of_not_ge hh) hSpos
    have hnonneg : 0≤ w*ell/2 := by positivity
    linarith
  have hS1 : success Γ i b≤ 1 := ((problem Γ i).outcome (two b)).success_le_one
  have hright := mul_le_mul_of_nonneg_left hS1 hδ
  have hwb : b≤ w := by linarith
  have hleft := mul_le_mul_of_nonneg_right hwb (by positivity : 0≤ ell/2)
  constructor
  · nlinarith
  · exact hwb

theorem actual_success_positive_of_relative_error
    (Γ : FiniteGame m 2 c Seed) (i : Fin m) (B : CanonicalEvent Γ)
    {t b e : ℝ} (hm : 1≤(m:ℝ)) (he : 0≤ e) (he1 : e<1)
    (hq : 0< comparisonMarginal Γ i B t b)
    (hD : canonicalDuplicate Γ i B b≤ comparisonMarginal Γ i B t b)
    (herror : |successError Γ i B t b|≤ e*comparisonMarginal Γ i B t b/m) :
    0< success Γ i b := by
  have hm0 : 0<(m:ℝ) := by linarith
  have heq : e*comparisonMarginal Γ i B t b/m≤ e*comparisonMarginal Γ i B t b := by
    apply (div_le_iff₀ hm0).2
    nlinarith [mul_nonneg he hq.le]
  have hlow := (abs_le.mp herror).1
  have hpositive : 0<(1-e)*comparisonMarginal Γ i B t b := by positivity
  unfold successError at hlow
  nlinarith

end Physical

theorem absorbed_source_error_tendsto_zero
    {e rent : ℕ→ℝ} {Nmax : ℝ}
    (he : Tendsto e atTop (𝓝 0))
    (hratio : Tendsto (fun m => e m/rent m) atTop (𝓝 0)) :
    Tendsto (fun m => 4*(1+(Nmax+4)/rent m)*e m) atTop (𝓝 0) := by
  have h := (he.const_mul 4).add (hratio.const_mul (4*(Nmax+4)))
  convert h using 1 <;> try ring
  ext m
  ring

end FCAppendix.Affine.Uniform07Finishing.Crossover
