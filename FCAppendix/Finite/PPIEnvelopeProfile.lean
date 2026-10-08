import FCAppendix.Finite.PPILocalEnvelope
import FCAppendix.Finite.PPIGaussianPrimitive

noncomputable section
namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Filter Set Topology

theorem envelope_scaled_increment_approx
    {n : ℕ} (P : Interim.Problem n) (v h L x ε : ℝ) (hh : 0 < h) (hLx : L ≤ x)
    (sel : ℝ → JointAction n)
    (hsel : ∀ᵐ w, w ∈ Icc (v + h * L) (v + h * x) → P.BestResponse w (sel w))
    (happrox : ∀ y ∈ Icc L x, ∀ act, P.BestResponse (v + h * y) act →
      |(P.outcome act).success - cdf (gaussianReal 0 1) y| ≤ ε) :
    |(P.envelope (v + h * x) - P.envelope (v + h * L)) / h -
      (gaussianSuccessPrimitive x - gaussianSuccessPrimitive L)| ≤ ε * (x - L) := by
  let s := fun w => derivWithin P.envelope (Ioi w) w
  have hsub (w z : ℝ) : P.envelope w + (z - w) * s w ≤ P.envelope z :=
    Subgradient.rightDeriv_subgradient P.envelope_convex (by simp) (by simp)
  have hab : v + h * L ≤ v + h * x := by nlinarith
  have hsubs : ∀ w ∈ Icc (v + h * L) (v + h * x),
      ∀ z ∈ Icc (v + h * L) (v + h * x), P.envelope w + (z - w) * s w ≤ P.envelope z :=
    fun w _ z _ => hsub w z
  have hint : IntervalIntegrable s volume (v + h * L) (v + h * x) :=
    Subgradient.intervalIntegrable hsubs ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩
  have heq : ∀ᵐ w, w ∈ Icc (v + h * L) (v + h * x) → (P.outcome (sel w)).success = s w := by
    apply Subgradient.ae_eq_of_ae_subgradient hsubs
    filter_upwards [hsel] with w hw hwI z _
    exact P.supporting_line w (sel w) (hw hwI) z
  let q := fun w => cdf (gaussianReal 0 1) ((w - v) / h)
  have hqc : Continuous q := continuous_Φ.comp (by fun_prop)
  have hqint : IntervalIntegrable q volume (v + h * L) (v + h * x) :=
    hqc.intervalIntegrable _ _
  have hqformula : (∫ w in (v + h * L)..(v + h * x), q w) =
      h * (gaussianSuccessPrimitive x - gaussianSuccessPrimitive L) := by
    have hz := intervalIntegral.smul_integral_comp_add_mul (a := L) (b := x) q h v
    have hz' : (fun y => q (v + h * y)) = (fun y => cdf (gaussianReal 0 1) y) := by
      funext y
      dsimp only [q]
      congr 1
      field_simp
      ring
    rw [hz', smul_eq_mul, integral_standardGaussianCDF] at hz
    exact hz.symm
  have herror : P.envelope (v + h * x) - P.envelope (v + h * L) -
      h * (gaussianSuccessPrimitive x - gaussianSuccessPrimitive L) =
      ∫ w in (v + h * L)..(v + h * x), s w - q w := by
    rw [intervalIntegral.integral_sub hint hqint, hqformula,
      ← P.envelope_sub_eq_integral_of_subgradient hab s (fun w _ z => hsub w z)]
  have hbound : |∫ w in (v + h * L)..(v + h * x), s w - q w| ≤
      ε * |(v + h * x) - (v + h * L)| := by
    rw [← Real.norm_eq_abs (∫ w in (v + h * L)..(v + h * x), s w - q w)]
    apply intervalIntegral.norm_integral_le_of_norm_le_const_ae
    filter_upwards [heq, hsel] with w hw hb hwI
    rw [uIoc_of_le hab] at hwI
    have hwI' := Ioc_subset_Icc_self hwI
    rw [Real.norm_eq_abs, ← hw hwI']
    have hy : (w - v) / h ∈ Icc L x := by
      constructor
      · apply (le_div_iff₀ hh).mpr
        nlinarith [hwI.1]
      · apply (div_le_iff₀ hh).mpr
        nlinarith [hwI.2]
    have hvw : v + h * ((w - v) / h) = w := by field_simp; ring
    have hhbr : P.BestResponse (v + h * ((w - v) / h)) (sel w) := by
      rw [hvw]
      exact hb hwI'
    exact happrox _ hy _ hhbr
  have hid : (P.envelope (v + h * x) - P.envelope (v + h * L)) / h -
      (gaussianSuccessPrimitive x - gaussianSuccessPrimitive L) =
      (P.envelope (v + h * x) - P.envelope (v + h * L) -
        h * (gaussianSuccessPrimitive x - gaussianSuccessPrimitive L)) / h := by
    field_simp
  rw [hid, abs_div, abs_of_pos hh]
  apply (div_le_iff₀ hh).mpr
  rw [herror]
  calc
    _ ≤ ε * |(v + h * x) - (v + h * L)| := hbound
    _ = ε * (x - L) * h := by
      rw [abs_of_nonneg (sub_nonneg.mpr hab)]
      ring

theorem envelope_profile_of_left_anchor
    {n : ℕ} (P : ℕ → Interim.Problem n) (v : ℝ) (scale : ℕ → ℝ)
    (hscale : Tendsto scale atTop (𝓝 0)) (hscale_pos : ∀ k, 0 < scale k)
    (d : ℝ) (hd : 0 < d) (sel : ℕ → ℝ → JointAction n)
    (hsel : ∀ k, ∀ᵐ w, w ∈ Ioo (v - d) (v + d) → (P k).BestResponse w (sel k w))
    (hcentral : ∀ R ≥ 0, ∀ ε > 0, ∀ᶠ k in atTop, ∀ x ∈ Icc (-R) R,
      ∀ act, (P k).BestResponse (v + scale k * x) act →
        |((P k).outcome act).success - cdf (gaussianReal 0 1) x| < ε)
    (hanchor : ∀ ε > 0, ∃ T₀ ≥ 0, ∀ T ≥ T₀, ∀ᶠ k in atTop,
      (P k).envelope (v - scale k * T) / scale k < ε)
    (R : ℝ) (hR : 0 ≤ R) :
    TendstoUniformlyOn (fun k x => (P k).envelope (v + scale k * x) / scale k)
      gaussianSuccessPrimitive atTop (Icc (-R) R) := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro η hη
  have hη3 : 0 < η / 3 := by positivity
  obtain ⟨T₀, hT₀, ha⟩ := hanchor (η / 3) hη3
  obtain ⟨T₁, hT₁⟩ := eventually_atTop.mp
    (gaussianSuccessPrimitive_neg_tendsto_zero.eventually (eventually_lt_nhds hη3))
  let T := max (max T₀ T₁) (R + 1)
  have hT0 : T₀ ≤ T := (le_max_left _ _).trans (le_max_left _ _)
  have hT1 : T₁ ≤ T := (le_max_right _ _).trans (le_max_left _ _)
  have hRT : R + 1 ≤ T := le_max_right _ _
  have hT : 0 < T := by linarith
  have hψsmall := hT₁ T hT1
  have hψpos := (gaussianSuccessPrimitive_neg_bounds hT).1
  let e := η / (3 * (2 * T + 1))
  have he : 0 < e := by dsimp [e]; positivity
  have hdscale : 0 < d / (T + 1) := by positivity
  filter_upwards [ha T hT0, hcentral T hT.le e he,
    hscale.eventually (eventually_lt_nhds hdscale)] with k hak hck hsk
  intro x hx
  have hxin : x ∈ Icc (-T) T := by constructor <;> linarith [hx.1, hx.2]
  have hlocal : Icc (v + scale k * (-T)) (v + scale k * x) ⊆ Ioo (v - d) (v + d) := by
    intro w hw
    have hsT : scale k * T < d := by
      have hh := (lt_div_iff₀ (by positivity : 0 < T + 1)).mp hsk
      nlinarith [hscale_pos k]
    constructor <;> nlinarith [hw.1, hw.2, hscale_pos k, hxin.2]
  have hbr : ∀ᵐ w, w ∈ Icc (v + scale k * (-T)) (v + scale k * x) →
      (P k).BestResponse w (sel k w) :=
    (hsel k).mono fun w hw hwI => hw (hlocal hwI)
  have hi := envelope_scaled_increment_approx (P k) v (scale k) (-T) x e
    (hscale_pos k) hxin.1 (sel k) hbr (fun y hy act hb =>
      (hck y ⟨hy.1, hy.2.trans hxin.2⟩ act hb).le)
  have he_len : e * (x - -T) < η / 3 := by
    have hh : e * (3 * (2 * T + 1)) = η := div_mul_cancel₀ _ (by positivity)
    nlinarith [hxin.2]
  have hUpos : 0 ≤ (P k).envelope (v - scale k * T) / scale k :=
    div_nonneg ((P k).envelope_nonneg _) (hscale_pos k).le
  rw [sub_div] at hi
  have heq : v + scale k * -T = v - scale k * T := by ring
  rw [heq] at hi
  rw [Real.dist_eq, abs_sub_comm]
  apply abs_lt.mpr
  constructor <;> linarith [(abs_le.mp hi).1, (abs_le.mp hi).2]

end FCAppendix.Bayes
