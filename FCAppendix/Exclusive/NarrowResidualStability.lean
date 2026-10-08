import FCAppendix.Exclusive.NarrowLocalIdentification
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable

namespace FCAppendix.Exclusive.Narrow
open MeasureTheory Set Filter Topology
open scoped BigOperators

theorem slope_bounds_of_derivative_bounds {l u k M : ℝ} {f f' : ℝ → ℝ}
    (hd : ∀ x ∈ Icc l u, HasDerivAt f (f' x) x)
    (hb : ∀ x ∈ Icc l u, f' x ∈ Icc k M) :
    ∀ x ∈ Icc l u, ∀ y ∈ Icc l u, x ≤ y →
      k * (y - x) ≤ f y - f x ∧ f y - f x ≤ M * (y - x) := by
  have hc : ContinuousOn f (Icc l u) := fun x hx =>
    (hd x hx).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ f (interior (Icc l u)) := fun x hx =>
    (hd x (interior_subset hx)).differentiableAt.differentiableWithinAt
  intro x hx y hy hxy
  constructor
  · apply (convex_Icc l u).mul_sub_le_image_sub_of_le_deriv hc hdiff _ x hx y hy hxy
    intro z hz
    rw [(hd z (interior_subset hz)).deriv]
    exact (hb z (interior_subset hz)).1
  · apply (convex_Icc l u).image_sub_le_mul_sub_of_deriv_le hc hdiff _ x hx y hy hxy
    intro z hz
    rw [(hd z (interior_subset hz)).deriv]
    exact (hb z (interior_subset hz)).2

private theorem abs_image_gap_ge {J : Set ℝ} {f : ℝ → ℝ} {k x y : ℝ}
    (hk : 0 ≤ k) (hx : x ∈ J) (hy : y ∈ J)
    (hlo : ∀ a ∈ J, ∀ b ∈ J, a ≤ b → k * (b - a) ≤ f b - f a) :
    k * |x - y| ≤ |f x - f y| := by
  rcases le_total x y with h | h
  · have hs := hlo x hx y hy h
    have hs0 : 0 ≤ f y - f x := (mul_nonneg hk (sub_nonneg.mpr h)).trans hs
    rw [abs_of_nonpos (sub_nonpos.mpr h), abs_of_nonpos (by linarith : f x - f y ≤ 0)]
    linarith
  · have hs := hlo y hy x hx h
    have hs0 : 0 ≤ f x - f y := (mul_nonneg hk (sub_nonneg.mpr h)).trans hs
    rw [abs_of_nonneg (sub_nonneg.mpr h), abs_of_nonneg hs0]
    exact hs

theorem exposure_gap_of_residuals {J : Set ℝ} {f hbase : ℝ → ℝ}
    {g lam tau v p q ep eq k Fmax : ℝ}
    (hk : 0 < k) (hp : p ∈ J) (hq : q ∈ J)
    (hf : |f q| ≤ Fmax)
    (hlo : ∀ x ∈ J, ∀ y ∈ J, x ≤ y →
      k * (y - x) ≤ (lam * f y + g * hbase y) - (lam * f x + g * hbase x))
    (hep : |v - (lam * f p + g * hbase p)| ≤ ep)
    (heq : |v - (tau * f q + g * hbase q)| ≤ eq) :
    k * |p - q| ≤ ep + eq + Fmax * |lam - tau| := by
  have hl := abs_image_gap_ge hk.le hp hq hlo
  have hid : (lam * f p + g * hbase p) - (lam * f q + g * hbase q) =
      ((lam * f p + g * hbase p) - v) +
      (v - (tau * f q + g * hbase q)) + (tau - lam) * f q := by ring
  have ha := abs_add_le (((lam * f p + g * hbase p) - v) +
      (v - (tau * f q + g * hbase q))) ((tau - lam) * f q)
  have hb := abs_add_le ((lam * f p + g * hbase p) - v)
      (v - (tau * f q + g * hbase q))
  have hc : |(lam * f p + g * hbase p) - v| ≤ ep := by
    rwa [abs_sub_comm]
  have hd : |(tau - lam) * f q| ≤ |lam - tau| * Fmax := by
    rw [abs_mul, abs_sub_comm tau lam]
    exact mul_le_mul_of_nonneg_left hf (abs_nonneg _)
  rw [hid] at hl
  nlinarith

theorem price_gap_of_residuals {μ : Measure ℝ} [IsFiniteMeasure μ]
    {J Lset : Set ℝ} {f hbase : ℝ → ℝ}
    {g lam tau rho sigma ep eq k M Fmin h : ℝ} {p q : ℝ → ℝ}
    (hh : 0 < h) (hmass : μ.real Set.univ = h)
    (hk : 0 < k) (hM : 0 ≤ M) (_hF : 0 < Fmin)
    (hlam : lam ∈ Lset) (htau : tau ∈ Lset)
    (hf : ∀ x ∈ J, Fmin ≤ f x)
    (hslopes : ∀ s ∈ Lset, ∀ x ∈ J, ∀ y ∈ J, x ≤ y →
      k * (y - x) ≤ (s * f y + g * hbase y) - (s * f x + g * hbase x) ∧
      (s * f y + g * hbase y) - (s * f x + g * hbase x) ≤ M * (y - x))
    (hp : Integrable p μ) (hq : Integrable q μ)
    (hpmem : ∀ᵐ v ∂μ, p v ∈ J) (hqmem : ∀ᵐ v ∂μ, q v ∈ J)
    (hpcap : ∫ v, p v ∂μ = rho) (hqcap : ∫ v, q v ∂μ = sigma)
    (hpres : ∀ᵐ v ∂μ, |v - (lam * f (p v) + g * hbase (p v))| ≤ ep)
    (hqres : ∀ᵐ v ∂μ, |v - (tau * f (q v) + g * hbase (q v))| ≤ eq) :
    |lam - tau| * Fmin ≤ ep + eq + M * |rho - sigma| / h := by
  have directional {s t r z e d : ℝ} {x y : ℝ → ℝ}
      (hst : s ≤ t) (hs : s ∈ Lset)
      (hx : Integrable x μ) (hy : Integrable y μ)
      (hxm : ∀ᵐ v ∂μ, x v ∈ J) (hym : ∀ᵐ v ∂μ, y v ∈ J)
      (hxc : ∫ v, x v ∂μ = r) (hyc : ∫ v, y v ∂μ = z)
      (hxr : ∀ᵐ v ∂μ, |v - (s * f (x v) + g * hbase (x v))| ≤ e)
      (hyr : ∀ᵐ v ∂μ, |v - (t * f (y v) + g * hbase (y v))| ≤ d) :
      (t - s) * Fmin ≤ e + d + M * |r - z| / h := by
    let A := (t - s) * Fmin - (e + d)
    by_cases hA : A ≤ 0
    · have hz : 0 ≤ M * |r - z| / h := div_nonneg (mul_nonneg hM (abs_nonneg _)) hh.le
      dsimp [A] at hA
      linarith
    · have hApos : 0 < A := lt_of_not_ge hA
      have hbound : ∀ᵐ v ∂μ, A ≤ M * (x v - y v) := by
        filter_upwards [hxm, hym, hxr, hyr] with v hvx hvy hex hey
        have he1 := (abs_le.mp hex).2
        have he2 := (abs_le.mp hey).1
        have hff := mul_le_mul_of_nonneg_left (hf (y v) hvy) (sub_nonneg.mpr hst)
        have hgap : A ≤ (s * f (x v) + g * hbase (x v)) -
            (s * f (y v) + g * hbase (y v)) := by
          dsimp [A]
          nlinarith
        have hyx : y v ≤ x v := by
          by_contra hn
          have hxy := (hslopes s hs (x v) hvx (y v) hvy (le_of_lt (lt_of_not_ge hn))).1
          have hn0 := mul_nonneg hk.le (sub_nonneg.mpr (le_of_lt (lt_of_not_ge hn)))
          linarith
        exact hgap.trans ((hslopes s hs (y v) hvy (x v) hvx hyx).2)
      have hi := integral_mono_ae (integrable_const A) ((hx.sub hy).const_mul M) hbound
      have hconst : (∫ _ : ℝ, A ∂μ) = h * A := by
        simp [integral_const, hmass, smul_eq_mul]
      have hright : (∫ v, M * (x v - y v) ∂μ) = M * (r - z) := by
        rw [integral_const_mul, integral_sub hx hy, hxc, hyc]
      change (∫ _ : ℝ, A ∂μ) ≤ ∫ v, M * (x v - y v) ∂μ at hi
      rw [hconst, hright] at hi
      have hi' : A * h ≤ M * |r - z| := by
        have hab := mul_le_mul_of_nonneg_left (le_abs_self (r - z)) hM
        nlinarith
      have hAd := (le_div_iff₀ hh).mpr hi'
      dsimp [A] at hAd
      linarith
  rcases le_total lam tau with h | h
  · have hdir := directional h hlam hp hq hpmem hqmem hpcap hqcap hpres hqres
    rw [abs_of_nonpos (sub_nonpos.mpr h)]
    nlinarith
  · have hdir := directional h htau hq hp hqmem hpmem hqcap hpcap hqres hpres
    rw [abs_sub_comm sigma rho] at hdir
    rw [abs_of_nonneg (sub_nonneg.mpr h)]
    nlinarith

private theorem real_cauchy_of_pair_error (x e : ℕ → ℝ)
    (he : Tendsto e atTop (𝓝 0)) (hb : ∀ t s, |x t - x s| ≤ e t + e s) :
    CauchySeq x := by
  apply Metric.cauchySeq_iff.mpr
  intro eps heps
  have hsmall : ∀ᶠ t in atTop, e t < eps / 2 :=
    (tendsto_order.mp he).2 _ (half_pos heps)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hsmall
  refine ⟨N, ?_⟩
  intro t ht s hs
  rw [Real.dist_eq]
  exact (hb t s).trans_lt (by linarith [hN t ht, hN s hs])

theorem full_sequence_of_finite_residuals {μ : Measure ℝ} [IsFiniteMeasure μ]
    {l u L U k M Fmin Fmax h g rho : ℝ} {f hbase : ℝ → ℝ}
    (hh : 0 < h) (hmass : μ.real Set.univ = h)
    (hk : 0 < k) (hM : 0 ≤ M) (hF : 0 < Fmin) (hFmax : 0 ≤ Fmax)
    (hf : ∀ p ∈ Icc l u, f p ∈ Icc Fmin Fmax)
    (hfc : ∀ p ∈ Icc l u, ContinuousAt f p)
    (hhc : ∀ p ∈ Icc l u, ContinuousAt hbase p)
    (hslopes : ∀ s ∈ Icc L U, ∀ x ∈ Icc l u, ∀ y ∈ Icc l u, x ≤ y →
      k * (y - x) ≤ (s * f y + g * hbase y) - (s * f x + g * hbase x) ∧
      (s * f y + g * hbase y) - (s * f x + g * hbase x) ≤ M * (y - x))
    (lam cap err : ℕ → ℝ) (p : ℕ → ℝ → ℝ)
    (hlam : ∀ t, lam t ∈ Icc L U)
    (hp : ∀ t, Integrable (p t) μ)
    (hpmem : ∀ t, ∀ᵐ v ∂μ, p t v ∈ Icc l u)
    (hpcap : ∀ t, ∫ v, p t v ∂μ = cap t)
    (hres : ∀ t, ∀ᵐ v ∂μ,
      |v - (lam t * f (p t v) + g * hbase (p t v))| ≤ err t)
    (hcap : Tendsto cap atTop (𝓝 rho)) (herr : Tendsto err atTop (𝓝 0)) :
    ∃ lamInf pInf,
      lamInf ∈ Icc L U ∧ Tendsto lam atTop (𝓝 lamInf) ∧
      (∀ᵐ v ∂μ, Tendsto (fun t => p t v) atTop (𝓝 (pInf v))) ∧
      LocalExposureSolution μ (Icc l u) f hbase g rho lamInf pInf := by
  classical
  let E : ℕ → ℝ := fun t => (err t + (M / h) * |cap t - rho|) / Fmin
  have hE : Tendsto E atTop (𝓝 0) := by
    have hh0 := (hcap.sub_const rho).abs
    simpa only [sub_self, abs_zero, mul_zero, add_zero, zero_div] using
      (herr.add (hh0.const_mul (M / h))).div_const Fmin
  have hprice : ∀ t s, |lam t - lam s| ≤ E t + E s := by
    intro t s
    have hb := price_gap_of_residuals hh hmass hk hM hF (hlam t) (hlam s)
      (fun z hz => (hf z hz).1) hslopes (hp t) (hp s) (hpmem t) (hpmem s)
      (hpcap t) (hpcap s) (hres t) (hres s)
    have htri : |cap t - cap s| ≤ |cap t - rho| + |cap s - rho| := by
      simpa [abs_sub_comm (cap s) rho] using abs_sub_le (cap t) rho (cap s)
    have hmul := mul_le_mul_of_nonneg_left htri (div_nonneg hM hh.le)
    have hb' : |lam t - lam s| * Fmin ≤
        err t + err s + (M / h) * (|cap t - rho| + |cap s - rho|) := by
      have hrw : M * |cap t - cap s| / h = (M / h) * |cap t - cap s| := by ring
      rw [hrw] at hb
      linarith
    have hb'' := (le_div_iff₀ hF).mpr hb'
    convert hb'' using 1 <;> first | rfl | (dsimp only [E]; ring)
  obtain ⟨lamInf, hlim⟩ := cauchySeq_tendsto_of_complete (real_cauchy_of_pair_error lam E hE hprice)
  have hlamInf : lamInf ∈ Icc L U := isClosed_Icc.mem_of_tendsto hlim (Eventually.of_forall hlam)
  let Good : ℝ → Prop := fun v => ∀ t,
    p t v ∈ Icc l u ∧ |v - (lam t * f (p t v) + g * hbase (p t v))| ≤ err t
  have hgood : ∀ᵐ v ∂μ, Good v := ae_all_iff.mpr fun t => (hpmem t).and (hres t)
  let D : ℕ → ℝ := fun t => (err t + Fmax * E t) / k
  have hD : Tendsto D atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero, zero_div] using
      (herr.add (hE.const_mul Fmax)).div_const k
  have hpair (v : ℝ) (hv : Good v) : ∀ t s, |p t v - p s v| ≤ D t + D s := by
    intro t s
    have hfabs : |f (p s v)| ≤ Fmax := by
      rw [abs_of_nonneg (hF.le.trans (hf _ (hv s).1).1)]
      exact (hf _ (hv s).1).2
    have hb := exposure_gap_of_residuals hk (hv t).1 (hv s).1 hfabs
      (fun x hx y hy hxy => (hslopes _ (hlam t) x hx y hy hxy).1) (hv t).2 (hv s).2
    have hm := mul_le_mul_of_nonneg_left (hprice t s) hFmax
    have hbd : |p t v - p s v| ≤ (err t + err s + Fmax * (E t + E s)) / k := by
      apply (le_div_iff₀ hk).mpr
      nlinarith
    convert hbd using 1
    dsimp [D]
    ring
  have hex : ∀ v : ℝ, ∃ z : ℝ, Good v → Tendsto (fun t => p t v) atTop (𝓝 z) := by
    intro v
    by_cases hv : Good v
    · obtain ⟨z, hz⟩ := cauchySeq_tendsto_of_complete
        (real_cauchy_of_pair_error (fun t => p t v) D hD (hpair v hv))
      exact ⟨z, fun _ => hz⟩
    · exact ⟨0, fun h => False.elim (hv h)⟩
  choose pInf hpInf using hex
  have hplim : ∀ᵐ v ∂μ, Tendsto (fun t => p t v) atTop (𝓝 (pInf v)) :=
    hgood.mono fun v hv => hpInf v hv
  have hpm : ∀ᵐ v ∂μ, pInf v ∈ Icc l u := by
    filter_upwards [hgood] with v hv
    exact isClosed_Icc.mem_of_tendsto (hpInf v hv) (Eventually.of_forall fun t => (hv t).1)
  let B := max |l| |u|
  have hbound {x : ℝ} (hx : x ∈ Icc l u) : ‖x‖ ≤ B := by
    rw [Real.norm_eq_abs]
    apply abs_le.mpr
    constructor
    · have hbl : |l| ≤ B := le_max_left _ _
      have hla : -|l| ≤ l := neg_abs_le l
      linarith [hx.1]
    · exact hx.2.trans ((le_abs_self u).trans (le_max_right _ _))
  have hmeas : AEStronglyMeasurable pInf μ :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun t => (hp t).aestronglyMeasurable) hplim
  have hpi : Integrable pInf μ := Integrable.of_bound hmeas B (hpm.mono fun _ hv => hbound hv)
  have hic := tendsto_integral_of_dominated_convergence (μ := μ) (fun _ => B)
    (fun t => (hp t).aestronglyMeasurable) (integrable_const B)
    (fun t => (hpmem t).mono fun _ hv => hbound hv) hplim
  have hcapacity : ∫ v, pInf v ∂μ = rho := by
    have hcc : Tendsto (fun t => ∫ v, p t v ∂μ) atTop (𝓝 rho) := by
      simpa only [hpcap] using hcap
    exact tendsto_nhds_unique hic hcc
  have heqn : ∀ᵐ v ∂μ, v = lamInf * f (pInf v) + g * hbase (pInf v) := by
    filter_upwards [hgood, hpm] with v hv hvinf
    have hPv := hpInf v hv
    have hphi := (hlim.mul ((hfc _ hvinf).tendsto.comp hPv)).add
      (((hhc _ hvinf).tendsto.comp hPv).const_mul g)
    have hz : Tendsto (fun t => v - (lam t * f (p t v) + g * hbase (p t v))) atTop (𝓝 0) := by
      apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
      exact squeeze_zero (fun _ => abs_nonneg _) (fun t => (hv t).2) herr
    have he := tendsto_nhds_unique hz (tendsto_const_nhds.sub hphi)
    linarith
  exact ⟨lamInf, pInf, hlamInf, hlim, hplim, hpi, hpm, heqn, hcapacity⟩

theorem full_sequence_from_tail {X : Type*} [TopologicalSpace X]
    (x : ℕ → X) (z : X) (T0 : ℕ)
    (h : Tendsto (fun t => x (t + T0)) atTop (𝓝 z)) :
    Tendsto x atTop (𝓝 z) :=
  (tendsto_add_atTop_iff_nat T0).mp h

theorem ae_full_sequence_from_tail {μ : Measure ℝ}
    (p : ℕ → ℝ → ℝ) (q : ℝ → ℝ) (T0 : ℕ)
    (h : ∀ᵐ v ∂μ, Tendsto (fun t => p (t + T0) v) atTop (𝓝 (q v))) :
    ∀ᵐ v ∂μ, Tendsto (fun t => p t v) atTop (𝓝 (q v)) :=
  h.mono fun v hv => full_sequence_from_tail (fun t => p t v) (q v) T0 hv

end FCAppendix.Exclusive.Narrow
