import FCAppendix.Ample.RouteIdentificationRateAlgebra
import FCAppendix.Ample.ActualNormalizationCore

noncomputable section
namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology Real
open scoped ENNReal BigOperators
open Ample Ample.DownstreamNormalizationCore

variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]

def scaledRouteAction (k : ℕ) (hk : k ≤ n) (b : ℝ) : JointAction n :=
  ⟨max 0 b, le_max_left _ _, k, hk⟩

def rankLowerEdge (n k : ℕ) (pi : ℕ → ℝ) : ℝ :=
  ∑ j ∈ Finset.Icc (k+1) n, pi j

@[simp] theorem scaledRouteAction_routeCount (k : ℕ) (hk : k ≤ n) (b : ℝ) :
    (scaledRouteAction k hk b).routeCount = k := rfl

@[simp] theorem scaledRouteAction_bid {k : ℕ} (hk : k ≤ n) {b : ℝ}
    (hb : 0 ≤ b) : (scaledRouteAction k hk b).bid = b :=
  max_eq_right hb

theorem affordable_cut_contradiction {M C : ℕ → ℕ}
    (Γ : ∀ t, FiniteGame (M t) n (C t) Seed) {g ell z w x : ℝ}
    {k : ℕ} (hk : k ≤ n) (hx : 0 < x) (hkx : (k : ℝ)*x < 1)
    (hw : ell < w) (hw0 : 0 ≤ w)
    (hM : ∀ᶠ t in atTop, 0 < M t)
    (hA : ∀ t, (Γ t).A = Schedule.ppi n)
    (hf : ∀ t, FreeDuplicateBase (Γ t))
    (hnorm : ActualNormalizationConclusion Γ g ell z)
    (hC : ∀ᶠ t in atTop, 0 < actualDeficit (Γ t) z)
    (hsmall : Tendsto (fun t =>
      actualFailure (Γ t) (scaledRouteAction k hk (x*actualDeficit (Γ t) z)) /
        actualDeficit (Γ t) z) atTop (𝓝 0)) : False := by
  let a := fun t => scaledRouteAction k hk (x*actualDeficit (Γ t) z)
  have hbound : ∀ᶠ t in atTop,
      actualDeficit (Γ t) w / actualDeficit (Γ t) z ≤
        w * (actualFailure (Γ t) (a t) / actualDeficit (Γ t) z) + (k : ℝ)*x := by
    filter_upwards [hM, hC] with t hmt hct
    have he := (actualMenu_isEnvelope (Γ t) hmt (hA t) (hf t) w hw0).1 (a t)
    have hl := (actualMenu_semantics (Γ t) hmt).2 (a t)
    have hb : (a t).bid = x*actualDeficit (Γ t) z :=
      scaledRouteAction_bid hk (mul_pos hx hct).le
    have hp := mul_le_mul_of_nonneg_left hl.2.2.2.1 (a t).bid_nonneg
    change actualDeficit (Γ t) w ≤
      w*actualFailure (Γ t) (a t) + (a t).bid*actualMeanLoad (Γ t) (a t) at he
    have hnum : actualDeficit (Γ t) w ≤
        w*actualFailure (Γ t) (a t) + ((k : ℝ)*x)*actualDeficit (Γ t) z := by
      rw [hb] at hp
      change x * actualDeficit (Γ t) z * actualMeanLoad (Γ t) (a t) ≤
        x * actualDeficit (Γ t) z * (k : ℝ) at hp
      rw [hb] at he
      nlinarith
    apply (div_le_iff₀ hct).2
    calc
      actualDeficit (Γ t) w ≤
          w*actualFailure (Γ t) (a t) + ((k : ℝ)*x)*actualDeficit (Γ t) z := hnum
      _ = (w * (actualFailure (Γ t) (a t) / actualDeficit (Γ t) z) +
          (k : ℝ)*x) * actualDeficit (Γ t) z := by
            field_simp [hct.ne']
  have hright : Tendsto (fun t =>
      w*(actualFailure (Γ t) (a t)/actualDeficit (Γ t) z)+(k : ℝ)*x)
      atTop (𝓝 ((k : ℝ)*x)) := by
    simpa only [mul_zero, zero_add] using
      (hsmall.const_mul w).add_const ((k : ℝ)*x)
  exact (not_le_of_gt hkx)
    (le_of_tendsto_of_tendsto (hnorm.pointwise w hw) hright hbound)

theorem exponential_upper_div_scale_zero {M : ℕ → ℕ} {p C : ℕ → ℝ}
    {J d : ℝ} (hM : Tendsto M atTop atTop) (hJd : J < d)
    (hp : ∀ᶠ t in atTop, 0 ≤ p t)
    (hupper : ∀ᶠ t in atTop, p t ≤ exp (-d * (M t : ℝ)))
    (hC : HasPopulationRate M C J) :
    Tendsto (fun t => p t / C t) atTop (𝓝 0) := by
  let b : ℝ := (J + d) / 2
  have hJb : J < b := by dsimp [b]; linarith
  have hbd : b < d := by dsimp [b]; linarith
  have hrate : ∀ᶠ t in atTop, populationLogRate (M t) (C t) < b :=
    hC.2.eventually_lt_const hJb
  have hbound : ∀ᶠ t in atTop, p t / C t ≤ exp (-(d-b) * (M t : ℝ)) := by
    filter_upwards [hp, hupper, hC.1, hrate, hM.eventually_ge_atTop 1]
      with t hp0 hpu hc hrt hm
    have hmR : (0 : ℝ) < M t := by exact_mod_cast (show 0 < M t by omega)
    have hlog : -b * (M t : ℝ) < log (C t) := by
      change -log (C t) / (M t : ℝ) < b at hrt
      have hh := (div_lt_iff₀ hmR).mp hrt
      linarith
    have hcl : exp (-b * (M t : ℝ)) ≤ C t := by
      rw [← exp_log hc]
      exact exp_le_exp.mpr hlog.le
    calc
      p t / C t ≤ exp (-d * (M t : ℝ)) / exp (-b * (M t : ℝ)) :=
        div_le_div₀ (exp_pos _).le hpu (exp_pos _) hcl
      _ = exp (-(d-b) * (M t : ℝ)) := by
        rw [← exp_sub]
        congr 1
        ring
  have he : Tendsto (fun t => exp (-(d-b) * (M t : ℝ))) atTop (𝓝 0) :=
    exp_neg_population_tendsto_zero hM (sub_pos.mpr hbd)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds he
    (by filter_upwards [hp, hC.1] with t hpt hct; exact div_nonneg hpt hct.le) hbound

lemma population_rate_eventual_upper {M : ℕ → ℕ} {p : ℕ → ℝ} {J d : ℝ}
    (hM : Tendsto M atTop atTop) (hp : HasPopulationRate M p J) (hd : d < J) :
    ∀ᶠ t in atTop, p t ≤ exp (-d*(M t : ℝ)) := by
  filter_upwards [hp.1, hp.2.eventually_const_lt hd,
    hM.eventually_ge_atTop 1] with t hpt hrt hmt
  have hmR : (0 : ℝ) < M t := by exact_mod_cast (show 0 < M t by omega)
  have hl : log (p t) < -d*(M t : ℝ) := by
    change d < -log (p t)/(M t : ℝ) at hrt
    have hh := (lt_div_iff₀ hmR).mp hrt
    linarith
  rw [← exp_log hpt]
  exact (exp_lt_exp.mpr hl).le

end FCAppendix.Bayes
