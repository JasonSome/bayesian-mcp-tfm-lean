import FCAppendix.PayOnce.ActualFirstOrder

namespace FCAppendix.PayOnce.RareSuccessSlope
open MeasureTheory Set OwnImpact

theorem phi_le_sq_mul_gap {n : ℕ} (hn : 2 ≤ n) {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) :
    phi n p ≤ (n : ℝ)^2 * (1-p) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hH := (H_bounds n (by omega) p hp.1 hp.2).2
  have hs := (div_le_iff₀ hnR).mp (Hslope_bounds hn hp).1
  have hs' := mul_le_mul_of_nonneg_left hs hnR.le
  have hnum : (n : ℝ)*H n p / Hslope n p ≤ (n : ℝ)^2 := by
    apply (div_le_iff₀ (Hslope_pos hn hp)).mpr
    nlinarith
  have hpow : (1-p)^(n-1) ≤ 1-p := by
    simpa only [pow_one] using pow_le_pow_of_le_one (sub_nonneg.mpr hp.2)
      (show 1-p ≤ 1 by linarith [hp.1]) (show 1 ≤ n-1 by omega)
  calc
    phi n p = ((n : ℝ)*H n p / Hslope n p) * (1-p)^(n-1) := by unfold phi; ring
    _ ≤ (n : ℝ)^2 * (1-p) :=
      mul_le_mul hnum hpow (pow_nonneg (sub_nonneg.mpr hp.2) _) (by positivity)

theorem weightedSlope_le_sq_mul_gap {n : ℕ} (hn : 2 ≤ n) {p weight : ℝ}
    (hp : p ∈ Icc (0 : ℝ) 1) (hw : 0 ≤ weight) :
    weightedSlope n p weight ≤ (n : ℝ)^2 * (1-p) := by
  unfold weightedSlope
  split_ifs
  · exact (mul_le_of_le_one_right (phi_nonneg hn hp) (by linarith)).trans (phi_le_sq_mul_gap hn hp)
  · exact mul_nonneg (by positivity) (sub_nonneg.mpr hp.2)

theorem marginal_le_success {n : ℕ} (hn : 0 < n) {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) :
    p ≤ success n p := by
  have hh : (1-p)^n ≤ 1-p := by
    simpa only [pow_one] using pow_le_pow_of_le_one (sub_nonneg.mpr hp.2)
      (show 1-p ≤ 1 by linarith [hp.1]) (show 1 ≤ n by omega)
  unfold success
  linarith

theorem mean_marginal_le_of_firstOrder {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ} (hn : 2 ≤ n)
    {p weight : Ω → ℝ} (hp : Measurable p) (hw : Measurable weight)
    (hbound : ∀ ω, p ω ∈ Icc (0 : ℝ) 1) (hweight : ∀ ω, weight ω ∈ Icc (0 : ℝ) 1)
    {b w ε M : ℝ} (hε : 0 < ε) (hb : ε ≤ b) (hM : 0 ≤ M) (hwM : w ≤ M)
    (hfirst : (∫ ω, success n (p ω) ∂μ) = (w-b) *
      ((∫ ω, weightedSlope n (p ω) (weight ω) ∂μ) / b)) :
    (∫ ω, p ω ∂μ) ≤ M * (n : ℝ)^2 / (ε + M*(n : ℝ)^2) := by
  let P := ∫ ω, p ω ∂μ
  let Q := ∫ ω, success n (p ω) ∂μ
  let D := ∫ ω, weightedSlope n (p ω) (weight ω) ∂μ
  have hpI := UnitInterval.integrable μ p hp (fun ω => (hbound ω).1) (fun ω => (hbound ω).2)
  have hQI := UnitInterval.integrable_success μ p hp (fun ω => (hbound ω).1) (fun ω => (hbound ω).2) n
  have hDI := integrable_weightedSlope μ hn hp hw hbound (fun ω _ => hweight ω)
  have hP0 : 0 ≤ P := integral_nonneg fun ω => (hbound ω).1
  have hD0 : 0 ≤ D := integral_nonneg fun ω => weightedSlope_nonneg hn (hbound ω) (fun _ => (hweight ω).2)
  have hPQ : P ≤ Q := integral_mono hpI hQI (fun ω => marginal_le_success (by omega) (hbound ω))
  have hD : D ≤ (n : ℝ)^2 * (1-P) := by
    have hh := integral_mono hDI (((integrable_const (1 : ℝ)).sub hpI).const_mul ((n : ℝ)^2))
      (fun ω => weightedSlope_le_sq_mul_gap hn (hbound ω) (hweight ω).1)
    simpa only [Pi.sub_apply, integral_const_mul, integral_sub (integrable_const _) hpI,
      integral_const, probReal_univ, one_smul, P, D] using hh
  have hb0 : 0 < b := hε.trans_le hb
  have hFOC : b*Q = (w-b)*D := by
    change Q = (w-b)*(D/b) at hfirst
    rw [hfirst]
    field_simp
  have hleft : ε*P ≤ b*Q :=
    (mul_le_mul_of_nonneg_right hb hP0).trans (mul_le_mul_of_nonneg_left hPQ hb0.le)
  have hright : b*Q ≤ M*((n : ℝ)^2*(1-P)) := by
    rw [hFOC]
    exact (mul_le_mul_of_nonneg_right (by linarith : w-b ≤ M) hD0).trans
      (mul_le_mul_of_nonneg_left hD hM)
  have hden : 0 < ε+M*(n : ℝ)^2 := by positivity
  apply (le_div_iff₀ hden).mpr
  change P*(ε+M*(n : ℝ)^2) ≤ M*(n : ℝ)^2
  nlinarith [hleft.trans hright]

end FCAppendix.PayOnce.RareSuccessSlope

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set
open scoped ProbabilityTheory BigOperators
variable {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem ae_actual_mean_marginal_bound {k : ℕ} (Γ : FiniteGame m (k+1) c Seed)
    (hk : 1 ≤ k) (hcm : c ≤ m)
    (hA : Γ.A = Schedule.once (k+1)) (hG : Γ.G = Schedule.once (k+1))
    (hu : UsersOptimal Γ) (B : PosteriorSystem Γ)
    (hB : PosteriorProposerOptimalAE Γ B) (hsym : SymmetricProposersOnPath Γ)
    (hatom : PositiveVisibleAtomless Γ)
    (hroute : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), x.2.routeCount = k+1)
    (hbid : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), 0 < x.2.bid) (i : Fin m)
    {ε M : ℝ} (hε : 0 < ε) (hM : 0 ≤ M) :
    ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), ε ≤ x.2.bid → x.1-Γ.g ≤ M →
      (∫ rivals, PayOnce.AnalyticalKernel.allocation (k+1) c (by omega)
        (by simpa only [card_rival_add_one] using hcm) rivals x.2.bid ∂analyticalRivalLaw Γ i) ≤
          M*((k+1 : ℕ) : ℝ)^2 / (ε+M*((k+1 : ℕ) : ℝ)^2) := by
  have hfoc := ae_actual_payOnce_weighted_first_order Γ hk hcm hA hG hu B hB hsym hatom hroute hbid i
  filter_upwards [hfoc] with x hx hxb hxM
  obtain ⟨weight, hw, hbound, _, _, hfirst⟩ := hx
  exact PayOnce.RareSuccessSlope.mean_marginal_le_of_firstOrder (analyticalRivalLaw Γ i)
    (by omega) (PayOnce.AnalyticalKernel.measurable_allocation_rivals _ _ (hε.trans_le hxb))
    hw (fun rivals => PayOnce.AnalyticalKernel.allocation_bounds _ _ rivals x.2.bid) hbound hε hxb hM hxM hfirst

end FCAppendix.Bayes

namespace FCAppendix.PayOnce.RareSuccessSlope
open MeasureTheory Set

theorem saturation_gap_pos {n : ℕ} {ε M : ℝ} (hε : 0 < ε) (hM : 0 ≤ M) :
    0 < ε / (ε+M*(n : ℝ)^2) := div_pos hε (by positivity)

theorem gap_le_one_sub_of_mean_bound {n : ℕ} {ε M P : ℝ}
    (hε : 0 < ε) (hM : 0 ≤ M)
    (hP : P ≤ M*(n : ℝ)^2 / (ε+M*(n : ℝ)^2)) :
    ε / (ε+M*(n : ℝ)^2) ≤ 1-P := by
  have hd : 0 < ε+M*(n : ℝ)^2 := by positivity
  have hbound := (le_div_iff₀ hd).mp hP
  apply (div_le_iff₀ hd).mpr
  nlinarith

end FCAppendix.PayOnce.RareSuccessSlope
