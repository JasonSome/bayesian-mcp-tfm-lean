import FCAppendix.Finite.PPIEnvelopeProfile

noncomputable section
namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Filter Set Topology

theorem div_profile_error_bound (u ψ s p a B e : ℝ)
    (ha : 0 < a) (hp : a ≤ p) (hs : a / 2 ≤ s) (hB : 0 ≤ B) (he : 0 ≤ e)
    (hu : |u - ψ| ≤ e) (hsp : |s - p| ≤ e) (hψ : |ψ| ≤ B) :
    |u / s - ψ / p| ≤ e * (2 / a + 2 * B / a ^ 2) := by
  have hspos : 0 < s := (half_pos ha).trans_le hs
  have hppos : 0 < p := ha.trans_le hp
  have hprod : a ^ 2 / 2 ≤ s * p := by nlinarith
  have hident : u / s - ψ / p = (u - ψ) / s + ψ * (p - s) / (s * p) := by
    field_simp
    ring
  rw [hident]
  calc
    _ ≤ |(u - ψ) / s| + |ψ * (p - s) / (s * p)| := abs_add_le _ _
    _ = |u - ψ| / s + |ψ| * |s - p| / (s * p) := by
      rw [abs_div, abs_div, abs_mul, abs_of_pos hspos, abs_of_pos (mul_pos hspos hppos),
        abs_sub_comm p s]
    _ ≤ e / s + (B * e) / (s * p) := add_le_add
      (div_le_div_of_nonneg_right hu hspos.le)
      (div_le_div_of_nonneg_right (mul_le_mul hψ hsp (abs_nonneg _) hB) (by positivity))
    _ ≤ e / (a / 2) + (B * e) / (a ^ 2 / 2) := add_le_add
      (div_le_div_of_nonneg_left he (half_pos ha) hs)
      (div_le_div_of_nonneg_left (mul_nonneg hB he) (by positivity) hprod)
    _ = _ := by ring

theorem bid_profile_of_uniform_envelope
    {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (M C : ℕ → ℕ) (Γ : ∀ k, FiniteGame (M k) n (C k) Seed)
    (hn : 0 < n) (i : ∀ k, Fin (M k)) (g t : ℝ)
    (hg : ∀ k, (Γ k).g = g) (scale : ℕ → ℝ) (hs : ∀ k, 0 < scale k)
    (R : ℝ) (hR : 0 ≤ R)
    (hU : TendstoUniformlyOn
      (fun k x => (problem (Γ k) (i k)).envelope (t + scale k * x) / scale k)
      gaussianSuccessPrimitive atTop (Icc (-R) R))
    (hcentral : ∀ δ > 0, ∀ᶠ k in atTop, ∀ x ∈ Icc (-R) R, ∀ act,
      (problem (Γ k) (i k)).BestResponse (t + scale k * x) act →
      act.routeCount = 1 ∧
        |((problem (Γ k) (i k)).outcome act).success - cdf (gaussianReal 0 1) x| < δ) :
    ∀ ε > 0, ∀ᶠ k in atTop, ∀ x ∈ Icc (-R) R, ∀ act,
      (problem (Γ k) (i k)).BestResponse (t + scale k * x) act →
      act.routeCount = 1 ∧
        |(act.bid - (t - g)) / scale k + gaussianPDFReal 0 1 x / cdf (gaussianReal 0 1) x| < ε := by
  have hcont : Continuous gaussianSuccessPrimitive := continuous_iff_continuousAt.mpr
    (fun x => (hasDerivAt_gaussianSuccessPrimitive x).continuousAt)
  obtain ⟨B, hB⟩ := (isCompact_Icc.image (continuous_abs.comp hcont)).bddAbove
  have hB' (x : ℝ) (hx : x ∈ Icc (-R) R) : |gaussianSuccessPrimitive x| ≤ B :=
    hB (mem_image_of_mem _ hx)
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB' 0 ⟨by linarith, hR⟩)
  let a := cdf (gaussianReal 0 1) (-R)
  have ha : 0 < a := CorrelatedLoads.gaussian_cdf_pos _
  let L := 2 / a + 2 * B / a ^ 2
  have hL : 0 ≤ L := by dsimp [L]; positivity
  intro ε hε
  let e := ε / (2 * (L + 1))
  have he : 0 < e := by dsimp [e]; positivity
  have heL : e * L < ε := by
    have hh : e * (2 * (L + 1)) = ε := div_mul_cancel₀ _ (by positivity)
    nlinarith
  have htol : 0 < min e (a / 2) := lt_min he (half_pos ha)
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hU e he,
    hcentral (min e (a / 2)) htol] with k huk hck
  intro x hx act hbr
  obtain ⟨hk, hclose⟩ := hck x hx act hbr
  refine ⟨hk, ?_⟩
  let u := (problem (Γ k) (i k)).envelope (t + scale k * x) / scale k
  let s := ((problem (Γ k) (i k)).outcome act).success
  let p := cdf (gaussianReal 0 1) x
  have hp : a ≤ p := monotone_cdf (gaussianReal 0 1) hx.1
  have hsp : a / 2 ≤ s := by
    have herror : |s - p| < a / 2 := hclose.trans_le (min_le_right _ _)
    linarith [(abs_lt.mp herror).1]
  have hu : |u - gaussianSuccessPrimitive x| ≤ e := by
    have hh := huk x hx
    rw [Real.dist_eq, abs_sub_comm] at hh
    exact hh.le
  have hquot := div_profile_error_bound u (gaussianSuccessPrimitive x) s p a B e ha hp hsp
    hB0 he.le hu (hclose.le.trans (min_le_left _ _)) (hB' x hx)
  have hq : |u / s - gaussianSuccessPrimitive x / p| < ε := hquot.trans_lt heL
  have hspos : 0 < s := (half_pos ha).trans_le hsp
  have hppos : 0 < p := ha.trans_le hp
  have heq := (problem (Γ k) (i k)).bestResponse_iff_attains (t + scale k * x) act |>.mp hbr
  rw [singleton_payoff (Γ k) hn (i k) act hk, hg k,
    ← singleton_success (Γ k) hn (i k) act hk] at heq
  have hbid : (act.bid - (t - g)) / scale k + gaussianPDFReal 0 1 x / p =
      -(u / s - gaussianSuccessPrimitive x / p) := by
    have hu_eq : u = (t + scale k * x - g - act.bid) * s / scale k := by
      dsimp only [u]
      rw [← heq]
    rw [hu_eq, gaussianSuccessPrimitive]
    change _ = -((t + scale k * x - g - act.bid) * s / scale k / s -
      (x * p + gaussianPDFReal 0 1 x) / p)
    have hscale_ne := (hs k).ne'
    field_simp [hscale_ne]
    ring
  change |(act.bid - (t - g)) / scale k + gaussianPDFReal 0 1 x / p| < ε
  rw [hbid, abs_neg]
  exact hq

end FCAppendix.Bayes
