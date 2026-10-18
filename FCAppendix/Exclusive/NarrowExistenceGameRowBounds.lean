import FCAppendix.Exclusive.NarrowExistenceGameParameter

noncomputable section
namespace FCAppendix.Exclusive.Narrow.Existence
open MeasureTheory Set Filter Topology

theorem finiteRowScore_decrease {m : ℕ} {V : Type*} (d c : ℕ)
    (a : UserTariff) (G : Schedule (d+1)) (p0 baseRatio : ℝ)
    (beta : V → ℝ) (v lo hi k : ℝ) (omega : RivalProfile m V)
    (hK : ∀ z ∈ Icc lo hi,
      k ≤ sourceStateCurvature d a G p0 (finiteRowState d c baseRatio beta v z omega))
    (x y : ℝ) (hx : x ∈ Icc lo hi) (hy : y ∈ Icc lo hi) (hxy : x ≤ y) :
    k*(y-x) ≤ finiteRowScore d c a G p0 baseRatio beta v x omega-
      finiteRowScore d c a G p0 baseRatio beta v y omega := by
  let f := fun z => -finiteRowScore d c a G p0 baseRatio beta v z omega-k*z
  have hd (z : ℝ) : HasDerivAt f
      (sourceStateCurvature d a G p0 (finiteRowState d c baseRatio beta v z omega)-k) z := by
    have hk : HasDerivAt (fun w : ℝ => k*w) k z := by
      simpa only [id_eq, mul_one] using (hasDerivAt_id z).const_mul k
    apply ((hasDerivAt_finiteRowScore d c a G p0 baseRatio beta v z omega).neg.sub hk).congr_deriv
    ring
  have hm := monotoneOn_of_deriv_nonneg (convex_Icc lo hi)
    (fun z _ => (hd z).continuousAt.continuousWithinAt)
    (fun z _ => (hd z).differentiableAt.differentiableWithinAt)
    (fun z hz => by rw [(hd z).deriv]; exact sub_nonneg.mpr (hK z (interior_subset hz)))
  have hh := hm hx hy hxy
  dsimp [f] at hh
  linarith

theorem finiteRowScore_bid_bound {m : ℕ} {V : Type*} (d c : ℕ)
    (a : UserTariff) (G : Schedule (d+1)) (p0 baseRatio : ℝ)
    (beta : V → ℝ) (v lo hi B : ℝ) (omega : RivalProfile m V)
    (hK : ∀ z ∈ Icc lo hi,
      |sourceStateCurvature d a G p0 (finiteRowState d c baseRatio beta v z omega)| ≤ B)
    (x y : ℝ) (hx : x ∈ Icc lo hi) (hy : y ∈ Icc lo hi) :
    |finiteRowScore d c a G p0 baseRatio beta v y omega-
      finiteRowScore d c a G p0 baseRatio beta v x omega| ≤ B*|y-x| := by
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z _ => (hasDerivAt_finiteRowScore d c a G p0 baseRatio beta v z omega).hasDerivWithinAt)
    (fun z hz => by simpa only [Real.norm_eq_abs, abs_neg] using hK z hz)
    (convex_Icc lo hi) hx hy
  simpa only [Real.norm_eq_abs] using hh

section Expected
variable {m : ℕ} {V : Type*} [TopologicalSpace V] [MeasurableSpace V]
  [BorelSpace V] [SecondCountableTopology V] [CompactSpace V]

theorem finiteExpectedScore_decrease (d c : ℕ) (a : UserTariff) (G : Schedule (d+1))
    (p0 baseRatio : ℝ) (h : unitInterval) (nu : Measure V) [IsProbabilityMeasure nu]
    (beta : V → ℝ) (hbeta : Continuous beta) (v lo hi : ℝ)
    (k : RivalProfile m V → ℝ) (hk : Integrable k (iidRivalLaw m h nu))
    (hK : ∀ omega z, z ∈ Icc lo hi →
      k omega ≤ sourceStateCurvature d a G p0 (finiteRowState d c baseRatio beta v z omega))
    (x y : ℝ) (hx : x ∈ Icc lo hi) (hy : y ∈ Icc lo hi) (hxy : x ≤ y) :
    (∫ omega, k omega ∂iidRivalLaw m h nu)*(y-x) ≤
      finiteExpectedScore (m := m) d c a G p0 baseRatio h nu beta v x-
        finiteExpectedScore (m := m) d c a G p0 baseRatio h nu beta v y := by
  have hix := integrable_finiteRowScore (m := m) d c a G p0 baseRatio h nu beta hbeta v x
  have hiy := integrable_finiteRowScore (m := m) d c a G p0 baseRatio h nu beta hbeta v y
  have hh := integral_mono (hk.mul_const (y-x)) (hix.sub hiy)
    (fun omega => finiteRowScore_decrease d c a G p0 baseRatio beta v lo hi
      (k omega) omega (hK omega) x y hx hy hxy)
  change (∫ omega, k omega*(y-x) ∂iidRivalLaw m h nu) ≤
    ∫ omega, finiteRowScore d c a G p0 baseRatio beta v x omega-
      finiteRowScore d c a G p0 baseRatio beta v y omega ∂iidRivalLaw m h nu at hh
  simpa only [integral_mul_const, integral_sub hix hiy, finiteExpectedScore] using hh

theorem finiteExpectedScore_parameter_bound (d c : ℕ) (hd : 1 ≤ d)
    (a : UserTariff) (G : Schedule (d+1)) (p0 baseRatio delta : ℝ) (hdelta : 0 ≤ delta)
    (h : unitInterval) (nu : Measure V) [IsProbabilityMeasure nu]
    (beta gamma : V → ℝ) (hbeta : Continuous beta) (hgamma : Continuous gamma)
    (hdiff : ∀ v, |gamma v-beta v| ≤ delta) (v z : ℝ)
    (L : RivalProfile m V → ℝ) (hL : Integrable L (iidRivalLaw m h nu))
    (hcross : ∀ omega t, t ∈ Icc (0:ℝ) 1 → |sourceStateInfluence d a G p0
      (finiteRowState d c baseRatio (interpolateLogBid beta gamma t) v z omega)| ≤ L omega) :
    |finiteExpectedScore (m := m) d c a G p0 baseRatio h nu gamma v z-
      finiteExpectedScore (m := m) d c a G p0 baseRatio h nu beta v z| ≤
        (∫ omega, L omega ∂iidRivalLaw m h nu)*delta := by
  have hib := integrable_finiteRowScore (m := m) d c a G p0 baseRatio h nu beta hbeta v z
  have hig := integrable_finiteRowScore (m := m) d c a G p0 baseRatio h nu gamma hgamma v z
  have hnorm := norm_integral_le_integral_norm (μ := iidRivalLaw m h nu)
    (fun omega => finiteRowScore d c a G p0 baseRatio gamma v z omega-
      finiteRowScore d c a G p0 baseRatio beta v z omega)
  have hmono := integral_mono (hig.sub hib).abs (hL.mul_const delta)
    (fun omega => finiteRowScore_parameter_bound d c hd a G p0 baseRatio delta
      (L omega) hdelta beta gamma hdiff v z omega (hcross omega))
  change |∫ omega, finiteRowScore d c a G p0 baseRatio gamma v z omega-
      finiteRowScore d c a G p0 baseRatio beta v z omega ∂iidRivalLaw m h nu| ≤ _
    at hnorm
  rw [integral_sub hig hib] at hnorm
  change (∫ omega, |finiteRowScore d c a G p0 baseRatio gamma v z omega-
      finiteRowScore d c a G p0 baseRatio beta v z omega| ∂iidRivalLaw m h nu) ≤ _ at hmono
  rw [integral_mul_const] at hmono
  exact hnorm.trans hmono

theorem finiteExpectedScore_bid_bound (d c : ℕ) (a : UserTariff) (G : Schedule (d+1))
    (p0 baseRatio : ℝ) (h : unitInterval) (nu : Measure V) [IsProbabilityMeasure nu]
    (beta : V → ℝ) (hbeta : Continuous beta) (v lo hi B : ℝ)
    (hK : ∀ (omega : RivalProfile m V) z, z ∈ Icc lo hi →
      |sourceStateCurvature d a G p0 (finiteRowState d c baseRatio beta v z omega)| ≤ B)
    (x y : ℝ) (hx : x ∈ Icc lo hi) (hy : y ∈ Icc lo hi) :
    |finiteExpectedScore (m := m) d c a G p0 baseRatio h nu beta v y-
      finiteExpectedScore (m := m) d c a G p0 baseRatio h nu beta v x| ≤ B*|y-x| := by
  have hix := integrable_finiteRowScore (m := m) d c a G p0 baseRatio h nu beta hbeta v x
  have hiy := integrable_finiteRowScore (m := m) d c a G p0 baseRatio h nu beta hbeta v y
  have hnorm := norm_integral_le_integral_norm (μ := iidRivalLaw m h nu)
    (fun omega => finiteRowScore d c a G p0 baseRatio beta v y omega-
      finiteRowScore d c a G p0 baseRatio beta v x omega)
  have hmono := integral_mono (hiy.sub hix).abs (integrable_const (B*|y-x|))
    (fun omega => finiteRowScore_bid_bound d c a G p0 baseRatio beta v lo hi B omega
      (hK omega) x y hx hy)
  change |∫ omega, finiteRowScore d c a G p0 baseRatio beta v y omega-
      finiteRowScore d c a G p0 baseRatio beta v x omega ∂iidRivalLaw m h nu| ≤ _
    at hnorm
  rw [integral_sub hiy hix] at hnorm
  simpa only [integral_const, probReal_univ, one_smul, finiteExpectedScore] using hnorm.trans hmono

end Expected
end FCAppendix.Exclusive.Narrow.Existence
