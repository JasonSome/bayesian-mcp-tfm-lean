import FCAppendix.Exclusive.NarrowExistenceGameRowBounds
import FCAppendix.Exclusive.NarrowExistenceGameNeighborhoodConstants
import FCAppendix.Exclusive.NarrowExistenceRareCounts

noncomputable section
namespace FCAppendix.Exclusive.Narrow.Existence
open MeasureTheory Set Filter Topology

def goodCount {V : Type*} (m : ℕ) (h eta : ℝ) : Set (RivalProfile m V) :=
  {omega | |(1+(activeCount omega : ℝ))/((m : ℝ)+1)-h| < eta}

theorem measurableSet_goodCount {V : Type*} [TopologicalSpace V] [MeasurableSpace V]
    [BorelSpace V] [SecondCountableTopology V] (m : ℕ) (h eta : ℝ) :
    MeasurableSet (goodCount (V := V) m h eta) := by
  have hc : Continuous (fun omega : RivalProfile m V =>
      |(1+(activeCount omega : ℝ))/((m : ℝ)+1)-h|) :=
    (continuous_of_discreteTopology : Continuous
      (fun N : ℕ => |(1+(N : ℝ))/((m : ℝ)+1)-h|)).comp continuous_activeCount
  exact (hc.isOpen_preimage (Iio eta) isOpen_Iio).measurableSet

def curvatureEnvelope {Ω : Type*} (E : Set Ω) (K B : ℝ) (omega : Ω) : ℝ :=
  (11/12:ℝ)*K-Eᶜ.indicator (fun _ => (11/12:ℝ)*K+B) omega

def influenceEnvelope {Ω : Type*} (E : Set Ω) (K B : ℝ) (omega : Ω) : ℝ :=
  (17/24:ℝ)*K+Eᶜ.indicator (fun _ => B) omega

theorem integrable_curvatureEnvelope {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu] (E : Set Ω) (hE : MeasurableSet E) (K B : ℝ) :
    Integrable (curvatureEnvelope E K B) mu :=
  (integrable_const _).sub ((integrable_const _).indicator hE.compl)

theorem integrable_influenceEnvelope {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu] (E : Set Ω) (hE : MeasurableSet E) (K B : ℝ) :
    Integrable (influenceEnvelope E K B) mu :=
  (integrable_const _).add ((integrable_const _).indicator hE.compl)

theorem integral_curvatureEnvelope {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu] (E : Set Ω) (hE : MeasurableSet E) (K B : ℝ) :
    (∫ omega, curvatureEnvelope E K B omega ∂mu) =
      (11/12:ℝ)*K-((11/12:ℝ)*K+B)*mu.real Eᶜ := by
  unfold curvatureEnvelope
  rw [integral_sub (integrable_const _) ((integrable_const _).indicator hE.compl),
    integral_const, integral_indicator_const _ hE.compl, smul_eq_mul]
  simp only [probReal_univ, smul_eq_mul, one_mul, mul_comm]

theorem integral_influenceEnvelope {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu] (E : Set Ω) (hE : MeasurableSet E) (K B : ℝ) :
    (∫ omega, influenceEnvelope E K B omega ∂mu) =
      (17/24:ℝ)*K+B*mu.real Eᶜ := by
  unfold influenceEnvelope
  rw [integral_add (integrable_const _) ((integrable_const _).indicator hE.compl),
    integral_const, integral_indicator_const _ hE.compl, smul_eq_mul]
  simp only [probReal_univ, smul_eq_mul, one_mul, mul_comm]

namespace UniformFiniteConstants
variable {d : ℕ} {G : Schedule (d+1)} {h rho : ℝ}
    (U : UniformFiniteConstants d G h rho)

theorem count_bad_bound (hh : h ∈ Icc (0:ℝ) 1) {m : ℕ} (hM : U.M0 ≤ m+1)
    (nu : Measure (ValueBand U.eps)) [IsProbabilityMeasure nu] :
    (iidRivalLaw m ⟨h,hh⟩ nu).real (goodCount m h U.eta)ᶜ ≤
      min (U.kappa/(48*U.B)) (U.kappa*U.delta/(48*U.B)) := by
  simpa only [goodCount, compl_setOf, not_lt] using U.rare hh hM nu

theorem expected_envelope_bounds (hh : h ∈ Icc (0:ℝ) 1) {m : ℕ} (hM : U.M0 ≤ m+1)
    (nu : Measure (ValueBand U.eps)) [IsProbabilityMeasure nu]
    (a : UserTariff) (ha : a.Allowed) :
    (7/8:ℝ)*literalReferenceCurvature d a (rho/h) ≤
      (∫ omega, curvatureEnvelope (goodCount m h U.eta)
        (literalReferenceCurvature d a (rho/h)) U.B omega ∂iidRivalLaw m ⟨h,hh⟩ nu) ∧
    (∫ omega, influenceEnvelope (goodCount m h U.eta)
      (literalReferenceCurvature d a (rho/h)) U.B omega ∂iidRivalLaw m ⟨h,hh⟩ nu) ≤
      (3/4:ℝ)*literalReferenceCurvature d a (rho/h) := by
  rw [integral_curvatureEnvelope _ _ (measurableSet_goodCount _ _ _),
    integral_influenceEnvelope _ _ (measurableSet_goodCount _ _ _)]
  have hp : 0 ≤ (iidRivalLaw m ⟨h,hh⟩ nu).real (goodCount m h U.eta)ᶜ := measureReal_nonneg
  have hb := U.count_bad_bound hh hM nu
  have hb' := (le_div_iff₀ (show 0 < 48*U.B from mul_pos (by norm_num) U.B_pos)).mp
    (hb.trans (min_le_left _ _))
  have href := U.reference a ha
  have hmul := mul_le_mul_of_nonneg_right href.2 hp
  have hk := mul_nonneg U.kappa_pos.le hp
  constructor <;> nlinarith [U.kappa_pos]

theorem expected_decrease (hh : h ∈ Icc (0:ℝ) 1) {m : ℕ} (c : ℕ)
    (hM : U.M0 ≤ m+1) (hC : |(c:ℝ)/((m:ℝ)+1)-rho| < U.eta)
    (nu : Measure (ValueBand U.eps)) [IsProbabilityMeasure nu]
    (a : UserTariff) (ha : a.Allowed) (baseRatio : ℝ) (hbase : baseRatio ∈ Icc (0:ℝ) U.eps)
    (beta : ValueBand U.eps → ℝ) (hbeta : Continuous beta)
    (hband : ∀ v, beta v ∈ Icc (-U.delta) U.delta)
    (v x y : ℝ) (hv : v ∈ Icc (1-U.eps) (1+U.eps))
    (hx : x ∈ Icc (-U.delta) U.delta) (hy : y ∈ Icc (-U.delta) U.delta) (hxy : x ≤ y) :
    (5/6:ℝ)*literalReferenceCurvature d a (rho/h)*(y-x) ≤
      finiteExpectedScore (m := m) d c a G (rho/h) baseRatio ⟨h,hh⟩ nu beta v x-
        finiteExpectedScore (m := m) d c a G (rho/h) baseRatio ⟨h,hh⟩ nu beta v y := by
  have hh' := finiteExpectedScore_decrease d c a G (rho/h) baseRatio ⟨h,hh⟩ nu beta hbeta
    v (-U.delta) U.delta (curvatureEnvelope (goodCount m h U.eta)
      (literalReferenceCurvature d a (rho/h)) U.B)
    (integrable_curvatureEnvelope _ _ (measurableSet_goodCount _ _ _) _ _)
    (fun omega z hz => by
      unfold curvatureEnvelope
      by_cases he : omega ∈ goodCount m h U.eta
      · rw [indicator_of_notMem (show omega ∉ (goodCount m h U.eta)ᶜ from fun hc => hc he), sub_zero]
        exact (U.good_rows (V := ValueBand U.eps) c hM hC a ha beta hband v z baseRatio hv hz hbase omega he).1
      · rw [indicator_of_mem (show omega ∈ (goodCount m h U.eta)ᶜ from he)]
        have hb := (U.all_rows (V := ValueBand U.eps) c hM hC a ha beta hband v z baseRatio hv hz hbase omega).2.1
        linarith [(abs_le.mp hb).1]) x y hx hy hxy
  have hk := (U.expected_envelope_bounds hh hM nu a ha).1
  have hpos : 0 < literalReferenceCurvature d a (rho/h) := U.kappa_pos.trans_le (U.reference a ha).1
  exact (mul_le_mul_of_nonneg_right (show (5/6:ℝ)*literalReferenceCurvature d a (rho/h) ≤ _ by
    linarith) (sub_nonneg.mpr hxy)).trans hh'

theorem expected_parameter_bound (hd : 1 ≤ d) (hh : h ∈ Icc (0:ℝ) 1) {m : ℕ} (c : ℕ)
    (hM : U.M0 ≤ m+1) (hC : |(c:ℝ)/((m:ℝ)+1)-rho| < U.eta)
    (nu : Measure (ValueBand U.eps)) [IsProbabilityMeasure nu]
    (a : UserTariff) (ha : a.Allowed) (baseRatio : ℝ) (hbase : baseRatio ∈ Icc (0:ℝ) U.eps)
    (beta gamma : ValueBand U.eps → ℝ) (hbeta : Continuous beta) (hgamma : Continuous gamma)
    (hband : ∀ v, beta v ∈ Icc (-U.delta) U.delta)
    (hgband : ∀ v, gamma v ∈ Icc (-U.delta) U.delta)
    (delta : ℝ) (hdelta : 0 ≤ delta) (hdiff : ∀ v, |gamma v-beta v| ≤ delta)
    (v z : ℝ) (hv : v ∈ Icc (1-U.eps) (1+U.eps)) (hz : z ∈ Icc (-U.delta) U.delta) :
    |finiteExpectedScore (m := m) d c a G (rho/h) baseRatio ⟨h,hh⟩ nu gamma v z-
      finiteExpectedScore (m := m) d c a G (rho/h) baseRatio ⟨h,hh⟩ nu beta v z| ≤
        (3/4:ℝ)*literalReferenceCurvature d a (rho/h)*delta := by
  have hh' := finiteExpectedScore_parameter_bound d c hd a G (rho/h) baseRatio delta hdelta
    ⟨h,hh⟩ nu beta gamma hbeta hgamma hdiff v z
    (influenceEnvelope (goodCount m h U.eta) (literalReferenceCurvature d a (rho/h)) U.B)
    (integrable_influenceEnvelope _ _ (measurableSet_goodCount _ _ _) _ _)
    (fun omega t ht => by
      have hi := interpolateLogBid_mem beta gamma (-U.delta) U.delta t hband hgband ht
      unfold influenceEnvelope
      by_cases he : omega ∈ goodCount m h U.eta
      · rw [indicator_of_notMem (show omega ∉ (goodCount m h U.eta)ᶜ from fun hc => hc he), add_zero]
        exact (U.good_rows (V := ValueBand U.eps) c hM hC a ha _ hi v z baseRatio hv hz hbase omega he).2
      · rw [indicator_of_mem (show omega ∈ (goodCount m h U.eta)ᶜ from he)]
        have hb := (U.all_rows (V := ValueBand U.eps) c hM hC a ha _ hi v z baseRatio hv hz hbase omega).2.2
        have hk : 0 ≤ literalReferenceCurvature d a (rho/h) :=
          (U.kappa_pos.trans_le (U.reference a ha).1).le
        linarith)
  exact hh'.trans (mul_le_mul_of_nonneg_right (U.expected_envelope_bounds hh hM nu a ha).2 hdelta)

theorem expected_central_bound (hh : h ∈ Icc (0:ℝ) 1) {m : ℕ} (c : ℕ)
    (hM : U.M0 ≤ m+1) (hC : |(c:ℝ)/((m:ℝ)+1)-rho| < U.eta)
    (nu : Measure (ValueBand U.eps)) [IsProbabilityMeasure nu]
    (a : UserTariff) (ha : a.Allowed) (baseRatio : ℝ) (hbase : baseRatio ∈ Icc (0:ℝ) U.eps)
    (v : ℝ) (hv : v ∈ Icc (1-U.eps) (1+U.eps)) :
    |finiteExpectedScore (m := m) d c a G (rho/h) baseRatio ⟨h,hh⟩ nu (fun _ => 0) v 0| ≤
      U.kappa*U.delta/24 := by
  have hz : (0:ℝ) ∈ Icc (-U.delta) U.delta := ⟨by linarith [U.delta_pos], U.delta_pos.le⟩
  have hi := integrable_finiteRowScore (m := m) d c a G (rho/h) baseRatio ⟨h,hh⟩ nu
    (fun _ => 0) continuous_const v 0
  have hh' := integral_good_upper (iidRivalLaw m ⟨h,hh⟩ nu)
    (fun omega => |finiteRowScore d c a G (rho/h) baseRatio (fun _ => 0) v 0 omega|)
    hi.abs (goodCount m h U.eta) (measurableSet_goodCount _ _ _)
    (U.kappa*U.delta/48) U.B
    (div_nonneg (mul_nonneg U.kappa_pos.le U.delta_pos.le) (by norm_num))
    (Filter.Eventually.of_forall (fun omega => (U.all_rows (V := ValueBand U.eps) c hM hC a ha (fun _ => 0)
      (fun _ => hz) v 0 baseRatio hv hz hbase omega).1))
    (Filter.Eventually.of_forall (fun omega he => U.central_rows (V := ValueBand U.eps) c hM hC a ha v baseRatio hv hbase omega he))
  have hnorm := norm_integral_le_integral_norm (μ := iidRivalLaw m ⟨h,hh⟩ nu)
    (finiteRowScore d c a G (rho/h) baseRatio (fun _ => 0) v 0)
  have hb := (le_div_iff₀ (show 0 < 48*U.B from mul_pos (by norm_num) U.B_pos)).mp
    ((U.count_bad_bound hh hM nu).trans (min_le_right _ _))
  change |finiteExpectedScore (m := m) d c a G (rho/h) baseRatio ⟨h,hh⟩ nu (fun _ => 0) v 0| ≤ _ at hnorm
  have hfinal := hnorm.trans hh'
  nlinarith

end UniformFiniteConstants
end FCAppendix.Exclusive.Narrow.Existence
