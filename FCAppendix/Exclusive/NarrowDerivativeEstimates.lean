import FCAppendix.Exclusive.NarrowInterimBridge
import Mathlib.Analysis.Calculus.MeanValue

namespace FCAppendix.Exclusive.Narrow.Finite
open MeasureTheory Filter Topology Set
open scoped BigOperators
variable {n m c : ℕ}

namespace Corridor
variable (P : Corridor n m c)

theorem ownBound_le_population {κ : ℝ} (hκ : 0 < κ)
    (hcap : κ * (m : ℝ) ≤ (c : ℝ) + 1) :
    P.ownBound ≤ (inverseBid n P.lower / (κ * inverseBid n P.upper)) / m := by
  have hm : (0 : ℝ) < m := by exact_mod_cast P.population
  have hw := inverseBid_pos n P.upper_pos
  calc
    P.ownBound ≤ inverseBid n P.lower / ((κ * m) * inverseBid n P.upper) :=
      div_le_div_of_nonneg_left (inverseBid_pos n P.lower_pos).le
        (mul_pos (mul_pos hκ hm) hw) (mul_le_mul_of_nonneg_right hcap hw.le)
    _ = _ := by field_simp [hκ.ne', hm.ne', hw.ne']

theorem pricePower_difference {N : ℕ} {W b x : ℝ} (h : P.ListBounds N W)
    (hb : b ∈ Icc P.lower P.upper) (hx : x ∈ Icc P.lower P.upper) :
    |P.pricePower N W x - P.pricePower N W b| ≤
      (P.radius / inverseBid n P.upper) * P.ownBound * |x - b| := by
  simpa only [Real.norm_eq_abs] using
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun y hy => (P.hasDerivAt_pricePower h hy).hasDerivWithinAt)
      (fun y hy => by simpa only [Real.norm_eq_abs] using P.pricePower_derivative_bound h hy)
      (convex_Icc P.lower P.upper) hb hx

end Corridor

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
namespace Row
variable {P : Corridor n m c} (R : Row P μ)

noncomputable def cost (a : UserTariff) (G : Schedule n) (g b : ℝ) : ℝ :=
  b * R.moment a.charge b + g * R.moment G.charge b
noncomputable def costDerivative (a : UserTariff) (G : Schedule n) (g b : ℝ) : ℝ :=
  R.moment a.charge b + b * R.momentDerivative a.charge b +
    g * R.momentDerivative G.charge b
noncomputable def referenceCostDerivative (a : UserTariff) (G : Schedule n) (g b : ℝ) : ℝ :=
  R.moment a.charge b + b * R.referenceDerivative a.charge b +
    g * R.referenceDerivative G.charge b

lemma hasDerivAt_cost (a : UserTariff) (G : Schedule n) (g : ℝ)
    {b : ℝ} (hb : b ∈ P.interior) :
    HasDerivAt (R.cost a G g) (R.costDerivative a G g b) b := by
  apply (((hasDerivAt_id b).mul (R.hasDerivAt_moment a.charge hb)).add
    ((R.hasDerivAt_moment G.charge hb).const_mul g)).congr_deriv
  dsimp only [costDerivative, id_eq]
  ring

theorem reference_foc_error (a : UserTariff) (ha : a.Allowed)
    (G : Schedule n) (g v : ℝ) {b : ℝ} (hb : b ∈ Icc P.lower P.upper)
    (hFOC : v * R.momentDerivative successIndicator b = R.costDerivative a G g b) :
    |v * R.referenceDerivative successIndicator b - R.referenceCostDerivative a G g b| ≤
      (2 * n * P.radius * (|v| + P.upper * n + |g| * n)) * P.ownBound := by
  have hs := R.derivative_error successIndicator (success_test_bound n) hb
  have ha' := R.derivative_error a.charge (tariff_test_bound n (by have := P.proposers; omega) a ha) hb
  have hg := R.derivative_error G.charge (schedule_test_bound G) hb
  have hbpos := P.lower_pos.trans_le hb.1
  have he : v * R.referenceDerivative successIndicator b - R.referenceCostDerivative a G g b =
      v * (R.referenceDerivative successIndicator b - R.momentDerivative successIndicator b) -
      b * (R.referenceDerivative a.charge b - R.momentDerivative a.charge b) -
      g * (R.referenceDerivative G.charge b - R.momentDerivative G.charge b) := by
    unfold referenceCostDerivative costDerivative at *
    linarith
  rw [he]
  calc
    _ ≤ |v * (R.referenceDerivative successIndicator b - R.momentDerivative successIndicator b)| +
        |b * (R.referenceDerivative a.charge b - R.momentDerivative a.charge b)| +
        |g * (R.referenceDerivative G.charge b - R.momentDerivative G.charge b)| :=
      (abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    _ ≤ |v| * (2 * n * 1 * P.radius * P.ownBound) +
        P.upper * (2 * n * (n:ℝ) * P.radius * P.ownBound) +
        |g| * (2 * n * (n:ℝ) * P.radius * P.ownBound) := by
      simp only [abs_mul, abs_sub_comm _ (R.momentDerivative successIndicator b),
        abs_sub_comm _ (R.momentDerivative a.charge b),
        abs_sub_comm _ (R.momentDerivative G.charge b)]
      exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left hs (abs_nonneg v))
        (mul_le_mul (by simpa only [abs_of_pos hbpos] using hb.2) ha'
          (abs_nonneg _) (P.upper_pos.le)))
        (mul_le_mul_of_nonneg_left hg (abs_nonneg g))
    _ = _ := by ring

end Row

namespace Row
variable {k : ℕ} {P : Corridor (k+1) m c} (R : Row P μ)

omit [IsProbabilityMeasure μ] in
lemma success_integrand_nonneg {b : ℝ} (hb : b ∈ Icc P.lower P.upper) :
    ∀ᵐ ω ∂μ, 0 ≤ binomialPolynomialDerivative (k+1) successIndicator (R.p b ω) * R.dp b ω := by
  filter_upwards [R.bounds] with ω hω
  rw [binomialPolynomialDerivative_success]
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _)
    (pow_nonneg (sub_nonneg.mpr (P.allocation_bounds hω hb).2) _))
      (P.velocity_bounds hω hb).1

theorem successDerivative_pos {b : ℝ} (hb : b ∈ Icc P.lower P.upper)
    (hover : μ {ω | c < R.count ω} ≠ 0) :
    0 < R.momentDerivative successIndicator b := by
  have hi := R.integrable_testDerivative successIndicator (success_test_bound (k+1)) hb
  apply (integral_pos_iff_support_of_nonneg_ae (R.success_integrand_nonneg hb) hi).mpr
  have hsub : {ω | c < R.count ω} ≤ᵐ[μ]
      Function.support (fun ω => binomialPolynomialDerivative (k+1) successIndicator (R.p b ω) * R.dp b ω) := by
    filter_upwards [R.bounds] with ω hω hcount
    change binomialPolynomialDerivative (k+1) successIndicator (R.p b ω) * R.dp b ω ≠ 0
    rw [binomialPolynomialDerivative_success]
    exact (mul_pos (mul_pos (by positivity)
      (pow_pos (sub_pos.mpr (P.allocation_lt_one hω hb hcount)) _))
        (P.velocity_pos hω hb hcount)).ne'
  exact (pos_iff_ne_zero.mpr hover).trans_le (measure_mono_ae hsub)

end Row
end FCAppendix.Exclusive.Narrow.Finite

namespace FCAppendix.Bayes.ExclusiveNarrow
open MeasureTheory ProbabilityTheory Game Exclusive Exclusive.Narrow
open Exclusive.Narrow.Finite Set Filter Topology
open scoped BigOperators ProbabilityTheory
variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem overload_positive (Γ : FiniteGame m n c Seed) (P : Corridor n m c)
    (hplay : CorridorPlay Γ P) (i : Fin m) (hcm : c < m)
    (hactive : userLaw Γ {u : UserDraw n | u.1.2.routeCount ≠ 0} ≠ 0) :
    userProfileLaw Γ {d | c < (gameRow Γ P hplay i).count d} ≠ 0 := by
  classical
  let A : Set (UserDraw n) := {u | u.1.2.routeCount ≠ 0}
  have hprod : userProfileLaw Γ (Set.univ.pi (fun _ : Fin m => A)) ≠ 0 := by
    rw [userProfileLaw, Measure.pi_pi]
    exact Finset.prod_ne_zero_iff.mpr (fun _ _ => hactive)
  have hsub : Set.univ.pi (fun _ : Fin m => A) ⊆
      {d | c < (gameRow Γ P hplay i).count d} := by
    intro d hd
    have hall : ∀ j, (d j).1.2.routeCount ≠ 0 := by
      intro j
      exact hd j (Set.mem_univ j)
    have he : activeRivals i d = Finset.univ.erase i := by
      ext j
      simp [activeRivals, hall]
    have hN : rivalCount i d = m := by
      rw [rivalCount, he, Finset.card_erase_of_mem (Finset.mem_univ i)]
      simp only [Finset.card_univ,Fintype.card_fin]
      have := P.population
      omega
    change c < rivalCount i d
    rwa [hN]
  exact mt (measure_mono_null hsub) hprod

end FCAppendix.Bayes.ExclusiveNarrow
