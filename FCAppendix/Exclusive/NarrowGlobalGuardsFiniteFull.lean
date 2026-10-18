import FCAppendix.Exclusive.NarrowGlobalGuardsFinite
import FCAppendix.Exclusive.NarrowGlobalGuardsFullReference

noncomputable section
namespace FCAppendix.Exclusive.Narrow.Global
open Set MeasureTheory ProbabilityTheory

theorem finite_full_route_compact_guard (d : ℕ) (hd : 1 ≤ d)
    (p0 B radius lower upper : ℝ) (hp0 : 0 < p0) (hp1 : p0 < 1)
    (hradius : 0 < radius) (hB : 0 ≤ B) (hlower : 0 < lower)
    (hprices : ∀ a : UserTariff, a.Allowed → normalizedPrice d a p0 ∈ Icc lower upper) :
    ∃ gap delta valueTolerance badTolerance : ℝ,
      0 < gap ∧ 0 < delta ∧ 0 < valueTolerance ∧ 0 < badTolerance ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] (mu : Measure Ω) [IsProbabilityMeasure mu]
        (E : Set Ω), MeasurableSet E → ∀ a : UserTariff, a.Allowed →
        ∀ G : Schedule (d+1), ∀ g v : ℝ, 0 ≤ g → v ≤ 2 →
        |v-1|+g*(d+1:ℕ) ≤ valueTolerance → ∀ b ∈ Icc (0:ℝ) B,
        radius ≤ |b-referenceCentralBid d a p0| →
        ∀ lam : Ω → ℝ, Measurable lam → (∀ w, 0 ≤ lam w) →
        (∀ w ∈ E, lam w ∈ Icc lower upper ∧
          |lam w-normalizedPrice d a p0| < delta) → mu.real Eᶜ ≤ badTolerance →
        (∫ w, LowType.binomialPayoff a G (d+1) g v b (activeDemand (d+1) b (lam w)) ∂mu)+gap ≤
          referenceUtility d a (normalizedPrice d a p0) 1 p0 := by
  obtain ⟨gamma,hgamma,hgap⟩ := referenceRawFullGap_uniform_compact d hd p0 B radius hp0 hp1 hradius
  obtain ⟨delta,hdelta,htransport⟩ := integral_binomialPayoff_compact_transport (d+1) (d+1)
    (by omega) (le_refl _) lower upper B (gamma/8) hlower (by positivity)
  let K : ℝ := 2+B*(d+1:ℕ)
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨gamma/2,delta,gamma/8,gamma/(4*K),by positivity,hdelta,by positivity,by positivity,?_⟩
  intro Ω _ mu _ E hE a ha G g v hg hv hvalue b hb houtside lam hlam hlam0 hgood hbad
  let C := pricedPayoff (d+1) (d+1) a b (normalizedPrice d a p0)+gamma/8+|v-1|+g*(d+1:ℕ)
  have hint := htransport mu E hE a ha G g v 2 hg (by norm_num) hv b hb
    (normalizedPrice d a p0) (hprices a ha) lam hlam hlam0 hgood
  change (∫ w, LowType.binomialPayoff a G (d+1) g v b (activeDemand (d+1) b (lam w)) ∂mu) ≤
    C+(2-C)*mu.real Eᶜ at hint
  have hr := hgap a ha b hb houtside
  change gamma ≤ referenceUtility d a (normalizedPrice d a p0) 1 p0-
    pricedPayoff (d+1) (d+1) a b (normalizedPrice d a p0) at hr
  have hC : C ≤ referenceUtility d a (normalizedPrice d a p0) 1 p0-3*gamma/4 := by
    dsimp [C]
    linarith only [hr,hvalue]
  have hlow := pricedPayoff_lower_bound (d+1) (d+1) (by omega) (le_refl _) a ha b B
    (normalizedPrice d a p0) hb (hlower.trans_le (hprices a ha).1)
  have hcoeff : 2-C ≤ K := by
    dsimp [K,C]
    nlinarith only [hlow,hgamma.le,abs_nonneg (v-1),
      mul_nonneg hg (Nat.cast_nonneg (d+1))]
  have hbadcost : (2-C)*mu.real Eᶜ ≤ gamma/4 := by
    have hm := mul_le_mul_of_nonneg_right hcoeff (measureReal_nonneg (μ := mu) (s := Eᶜ))
    have hbprob := (le_div_iff₀ (mul_pos (by norm_num : (0:ℝ)<4) hK)).mp hbad
    nlinarith only [hm,hbprob]
  linarith only [hint,hC,hbadcost]

end FCAppendix.Exclusive.Narrow.Global
