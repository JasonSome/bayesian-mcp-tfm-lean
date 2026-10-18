import FCAppendix.Exclusive.NarrowExistenceGameExpected
import FCAppendix.Exclusive.NarrowExistenceGameUtility

noncomputable section
namespace FCAppendix.Exclusive.Narrow.Existence
open MeasureTheory ProbabilityTheory Set Filter Topology

namespace UniformFiniteConstants
variable {d : ℕ} {G : Schedule (d+1)} {h rho : ℝ}
    (W : UniformFiniteConstants d G h rho)
variable {V : Type} [TopologicalSpace V] [MeasurableSpace V]
    [BorelSpace V] [SecondCountableTopology V] [CompactSpace V]

theorem wide_expected_decrease_of_count_bound
    (hh : h ∈ Icc (0 : ℝ) 1) {m : ℕ} (c : ℕ)
    (hM : W.M0 ≤ m+1) (hC : |(c : ℝ)/((m : ℝ)+1)-rho| < W.eta)
    (nu : Measure V) [IsProbabilityMeasure nu]
    (a : UserTariff) (ha : a.Allowed) (baseRatio : ℝ)
    (hbase : baseRatio ∈ Icc (0 : ℝ) W.eps)
    (beta : V → ℝ) (hbeta : Continuous beta)
    (hband : ∀ v, beta v ∈ Icc (-W.delta) W.delta)
    (hbad : (iidRivalLaw m ⟨h,hh⟩ nu).real (goodCount m h W.eta)ᶜ ≤ W.kappa/(48*W.B))
    (v x y : ℝ) (hv : v ∈ Icc (1-W.eps) (1+W.eps))
    (hx : x ∈ Icc (-W.delta) W.delta) (hy : y ∈ Icc (-W.delta) W.delta) (hxy : x ≤ y) :
    (5/6 : ℝ)*literalReferenceCurvature d a (rho/h)*(y-x) ≤
      finiteExpectedScore (m := m) d c a G (rho/h) baseRatio ⟨h,hh⟩ nu beta v x-
        finiteExpectedScore (m := m) d c a G (rho/h) baseRatio ⟨h,hh⟩ nu beta v y := by
  let E := goodCount (V := V) m h W.eta
  let mu := iidRivalLaw m ⟨h,hh⟩ nu
  let K := literalReferenceCurvature d a (rho/h)
  have hE : MeasurableSet E := measurableSet_goodCount m h W.eta
  have hh' := finiteExpectedScore_decrease d c a G (rho/h) baseRatio ⟨h,hh⟩ nu beta hbeta
    v (-W.delta) W.delta (curvatureEnvelope E K W.B)
    (integrable_curvatureEnvelope mu E hE K W.B)
    (fun omega z hz => by
      unfold curvatureEnvelope
      by_cases he : omega ∈ E
      · rw [indicator_of_notMem (show omega ∉ Eᶜ from fun hc => hc he), sub_zero]
        exact (W.good_rows c hM hC a ha beta hband v z baseRatio hv hz hbase omega he).1
      · rw [indicator_of_mem (show omega ∈ Eᶜ from he)]
        have hb := (W.all_rows c hM hC a ha beta hband v z baseRatio hv hz hbase omega).2.1
        linarith [(abs_le.mp hb).1]) x y hx hy hxy
  have henv : (7/8 : ℝ)*K ≤ ∫ omega, curvatureEnvelope E K W.B omega ∂mu := by
    rw [integral_curvatureEnvelope mu E hE]
    have hp : 0 ≤ mu.real Eᶜ := measureReal_nonneg
    have hb := (le_div_iff₀ (show 0 < 48*W.B from mul_pos (by norm_num) W.B_pos)).mp hbad
    have href := W.reference a ha
    have hmul := mul_le_mul_of_nonneg_right href.2 hp
    have hk := mul_nonneg W.kappa_pos.le hp
    dsimp [K, mu, E] at *
    nlinarith [W.kappa_pos]
  have hpos : 0 < K := W.kappa_pos.trans_le (W.reference a ha).1
  exact (mul_le_mul_of_nonneg_right (show (5/6 : ℝ)*K ≤ _ by linarith)
    (sub_nonneg.mpr hxy)).trans hh'

omit [TopologicalSpace V] [BorelSpace V] [SecondCountableTopology V] [CompactSpace V] in
theorem exists_wide_action_count_threshold (hh : h ∈ Icc (0 : ℝ) 1) :
    ∃ M0 : ℕ, ∀ m ≥ M0, ∀ (nu : Measure V) [IsProbabilityMeasure nu],
      (iidRivalLaw m ⟨h,hh⟩ nu).real (goodCount m h W.eta)ᶜ ≤ W.kappa/(48*W.B) := by
  obtain ⟨M0, hM0⟩ := exists_count_bad_probability_bound (V := V) ⟨h,hh⟩ W.eta_pos
    (probability := W.kappa/(48*W.B))
    (div_pos W.kappa_pos (mul_pos (by norm_num) W.B_pos))
  refine ⟨M0, ?_⟩
  intro m hm nu _
  simpa only [goodCount, compl_setOf, not_lt] using (hM0 m hm nu).le

theorem wide_utility_maximizes_of_root
    (hh : h ∈ Icc (0 : ℝ) 1) {m : ℕ} (c : ℕ)
    (hM : W.M0 ≤ m+1) (hC : |(c : ℝ)/((m : ℝ)+1)-rho| < W.eta)
    (nu : Measure V) [IsProbabilityMeasure nu]
    (a : UserTariff) (ha : a.Allowed) (baseRatio : ℝ)
    (hbase : baseRatio ∈ Icc (0 : ℝ) W.eps)
    (beta : V → ℝ) (hbeta : Continuous beta)
    (hband : ∀ v, beta v ∈ Icc (-W.delta) W.delta)
    (hbad : (iidRivalLaw m ⟨h,hh⟩ nu).real (goodCount m h W.eta)ᶜ ≤ W.kappa/(48*W.B))
    (v b : ℝ) (hv : v ∈ Icc (1-W.eps) (1+W.eps)) (hb : b ∈ Icc (-W.delta) W.delta)
    (hroot : finiteExpectedScore (m := m) d c a G (rho/h) baseRatio ⟨h,hh⟩ nu beta v b = 0)
    (z : ℝ) (hz : z ∈ Icc (-W.delta) W.delta) :
    finiteExpectedUtility (m := m) d c a G (rho/h) baseRatio ⟨h,hh⟩ nu beta v z ≤
      finiteExpectedUtility (m := m) d c a G (rho/h) baseRatio ⟨h,hh⟩ nu beta v b := by
  apply finiteExpectedUtility_maximizes_of_decrease d c a G (rho/h) baseRatio ⟨h,hh⟩ nu
    beta hbeta v (-W.delta) W.delta ((5/6 : ℝ)*literalReferenceCurvature d a (rho/h)) b
    (mul_pos (by norm_num) (W.kappa_pos.trans_le (W.reference a ha).1)) hb hroot
  · exact fun x hx y hy hxy => W.wide_expected_decrease_of_count_bound hh c hM hC nu a ha
      baseRatio hbase beta hbeta hband hbad v x y hv hx hy hxy
  · exact hz

end UniformFiniteConstants
end FCAppendix.Exclusive.Narrow.Existence
