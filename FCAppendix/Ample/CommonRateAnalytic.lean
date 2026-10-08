import FCAppendix.Ample.CommonRateActualAdapters
import FCAppendix.Ample.BoundaryRates

noncomputable section
namespace FCAppendix.Ample
open Finset Filter Topology Set Real
open scoped BigOperators

theorem commonRate_common_positive {α : Type*} (s : Finset α) (f : α → ℝ)
    (hf : ∀ x ∈ s, 0 < f x) : ∃ d > 0, ∀ x ∈ s, d < f x := by
  classical
  revert hf
  induction s using Finset.induction_on with
  | empty =>
    intro _
    exact ⟨1, by norm_num, by simp⟩
  | @insert a s _ha ih =>
    intro hf
    obtain ⟨d, hd, hds⟩ := ih (fun x hx => hf x (mem_insert_of_mem hx))
    refine ⟨min (f a / 2) d, lt_min (half_pos (hf a (mem_insert_self _ _))) hd, ?_⟩
    intro x hx
    rcases mem_insert.mp hx with hxa | hx
    · subst x
      exact (min_le_left _ _).trans_lt (half_lt_self (hf a (mem_insert_self _ _)))
    · exact (min_le_right _ _).trans_lt (hds x hx)

theorem commonRate_congest_antitone {n N c k l : ℕ} {lam : ℕ → ℝ}
    (hlam : ValidLaw n lam) (hkl : k ≤ l) :
    congestProb n N c l lam ≤ congestProb n N c k lam := by
  classical
  unfold congestProb congestProbAt
  apply Finset.sum_le_sum
  intro x _
  apply mul_le_mul_of_nonneg_left _
    (Finset.prod_nonneg fun i _ => contactWeight_nonneg hlam (x i))
  by_cases hl : ∀ j ∈ selected n l, c ≤ contacts x j
  · have hk : ∀ j ∈ selected n k, c ≤ contacts x j :=
      fun j hj => hl j (selected_mono hkl hj)
    simp only [if_pos hl, if_pos hk, le_refl]
  · simp only [if_neg hl]
    split_ifs <;> norm_num

theorem commonRate_congest_domination {n N c k : ℕ}
    {pi lam : ℕ → ℝ} (hpi : ValidLaw n pi) {a : ℝ} (ha : 0 ≤ a)
    (hdom : ∀ T : Finset (Fin n), a * contactWeight n pi T ≤ contactWeight n lam T) :
    a ^ N * congestProb n N c k pi ≤ congestProb n N c k lam := by
  classical
  unfold congestProb congestProbAt
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x _
  have hp : a ^ N * (∏ i : Fin N, contactWeight n pi (x i)) ≤
      ∏ i : Fin N, contactWeight n lam (x i) := by
    calc
      _ = ∏ i : Fin N, a * contactWeight n pi (x i) := by
        rw [Finset.prod_mul_distrib]
        simp
      _ ≤ _ := Finset.prod_le_prod
        (fun i _ => mul_nonneg ha (contactWeight_nonneg hpi (x i)))
        (fun i _ => hdom (x i))
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hp
    (show 0 ≤ (if ∀ j ∈ selected n k, c ≤ contacts x j then (1 : ℝ) else 0) by
      split_ifs <;> norm_num)

theorem commonRate_fullMGF_eq {n : ℕ} {h : ℝ} {pi : ℕ → ℝ}
    (hmass : ∑ j ∈ Finset.Icc 1 n, pi j = h) (t : ℝ) :
    rivalMGF n n pi t = fullMGF n h pi t := by
  change prefixMGF n n pi t = _
  exact prefixMGF_self_eq_fullMGF hmass t

theorem commonRate_fullObjective_eq {n : ℕ} {h rho : ℝ} {pi : ℕ → ℝ}
    (hmass : ∑ j ∈ Finset.Icc 1 n, pi j = h) (t : ℝ) :
    rivalObjective n rho n pi t = fullObjective n rho h pi t := by
  simp only [rivalObjective, fullObjective, commonRate_fullMGF_eq hmass]

theorem commonRate_fullRate_eq {n : ℕ} {h rho : ℝ} {pi : ℕ → ℝ}
    (hmass : ∑ j ∈ Finset.Icc 1 n, pi j = h) :
    rivalRate n rho n pi = fullRate n rho h pi := by
  unfold rivalRate fullRate
  simp only [commonRate_fullObjective_eq hmass]

theorem commonRate_objective_unbounded {n r : ℕ} {h rho : ℝ} {pi : ℕ → ℝ}
    (hpi : ValidLaw n pi) (hmass : ∑ j ∈ Finset.Icc 1 n, pi j = h)
    (hr : r ∈ Finset.Icc 1 n) (hpr : 0 < pi r)
    (htop : ∀ j ∈ Finset.Icc (r+1) n, pi j = 0)
    (hgap : (r : ℝ) < n*rho) (B : ℝ) :
    ∃ t ≥ 0, B < fullObjective n rho h pi t := by
  let t : ℝ := (|B| + 1) / (n*rho - r)
  have ht : 0 < t := div_pos (by positivity) (sub_pos.mpr hgap)
  have hexp : 1 ≤ exp ((r : ℝ)*t) := one_le_exp (mul_nonneg (show (0 : ℝ) ≤ r by exact_mod_cast (Nat.zero_le 1).trans (Finset.mem_Icc.mp hr).1) ht.le)
  have hsum : (∑ j ∈ Finset.Icc 1 n, pi j * exp ((j : ℝ)*t)) ≤ h * exp ((r : ℝ)*t) := by
    rw [← hmass, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro j hj
    by_cases hjr : j ≤ r
    · exact mul_le_mul_of_nonneg_left
        (exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by exact_mod_cast hjr) ht.le))
        (hpi.nonneg j hj)
    · rw [htop j (Finset.mem_Icc.mpr ⟨by omega, (Finset.mem_Icc.mp hj).2⟩)]
      simp
  have hupper : fullMGF n h pi t ≤ exp ((r : ℝ)*t) := by
    have hh : h ≤ 1 := hmass ▸ hpi.total_le
    have hh0 : 0 ≤ 1-h := sub_nonneg.mpr hh
    have hhE := mul_le_mul_of_nonneg_left hexp hh0
    unfold fullMGF
    nlinarith
  have hpos : 0 < fullMGF n h pi t := by
    have hp := mul_pos hpr (exp_pos ((r : ℝ)*t))
    have hs := Finset.single_le_sum (s := Finset.Icc 1 n)
      (f := fun j => pi j * exp ((j : ℝ)*t))
      (fun j hj => mul_nonneg (hpi.nonneg j hj) (exp_pos _).le) hr
    have hh : h ≤ 1 := hmass ▸ hpi.total_le
    unfold fullMGF
    linarith
  have hlog := log_le_log hpos hupper
  rw [log_exp] at hlog
  have he : (n*rho-r)*t = |B|+1 := by
    dsimp [t]
    field_simp [ne_of_gt (sub_pos.mpr hgap)]
  refine ⟨t, ht.le, ?_⟩
  unfold fullObjective
  nlinarith [le_abs_self B]

theorem commonRate_optimizer_unique {Ω : Type*} [Fintype Ω]
    {mu : FiniteLaw Ω} {X : Ω → ℝ} {r t : ℝ}
    (hi : FiniteCramer.Interior mu X r) (ht : FiniteCramer.mean mu X t = r)
    {s : ℝ} (he : FiniteCramer.objective mu X r s = FiniteCramer.objective mu X r t) :
    s = t := by
  let f : ℝ → ℝ := FiniteCramer.objective mu X r
  have hd (u : ℝ) : HasDerivAt f (r-FiniteCramer.mean mu X u) u := by
    have hh := ((hasDerivAt_id u).const_mul r).sub (FiniteCramer.hasDerivAt_cgf mu X u)
    have hh' : HasDerivAt f (r * 1 - FiniteCramer.mean mu X u) u :=
      hh.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun _ => rfl))
    simpa only [mul_one] using hh'
  have hcont : Continuous f := continuous_iff_continuousAt.mpr (fun u => (hd u).continuousAt)
  rcases lt_trichotomy s t with hst | heq | hts
  · have hm : StrictMonoOn f (Icc s t) := by
      apply strictMonoOn_of_deriv_pos (convex_Icc s t) hcont.continuousOn
      intro u hu
      have hu' : u ∈ Ioo s t := by simpa only [interior_Icc] using hu
      rw [(hd u).deriv, ← ht]
      exact sub_pos.mpr (FiniteCramer.strictMono_mean hi hu'.2)
    have hh := hm (by simp [hst.le]) (by simp [hst.le]) hst
    exact False.elim ((ne_of_lt hh) he)
  · exact heq
  · have hm : StrictAntiOn f (Icc t s) := by
      apply strictAntiOn_of_deriv_neg (convex_Icc t s) hcont.continuousOn
      intro u hu
      have hu' : u ∈ Ioo t s := by simpa only [interior_Icc] using hu
      rw [(hd u).deriv, ← ht]
      exact sub_neg.mpr (FiniteCramer.strictMono_mean hi hu'.1)
    have hh := hm (by simp [hts.le]) (by simp [hts.le]) hts
    exact False.elim ((ne_of_lt hh) he)

theorem commonRate_full_optimizer {n : ℕ} (hn : 0 < n)
    {h rho : ℝ} {pi : ℕ → ℝ} (hpi : ValidLaw n pi)
    (hmass : ∑ j ∈ Finset.Icc 1 n, pi j = h)
    (hmean : contactMarginal n pi < rho) (hrho : rho < 1) (hpn : 0 < pi n) :
    0 < fullRate n rho h pi ∧
    ∃ t > 0, fullObjective n rho h pi t = fullRate n rho h pi ∧
      (∀ s ≥ 0, fullObjective n rho h pi s ≤ fullRate n rho h pi) ∧
      (∀ s ≥ 0, fullObjective n rho h pi s = fullRate n rho h pi → s=t) := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hi := contactLaw_interior (show 1 ≤ n by omega) le_rfl hpi hmean
    ⟨n, Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩, hpn, by simp; nlinarith⟩
  let mu := contactLaw n pi hpi
  let X := SimultaneousCongestion.count (selected n n)
  have hrewrite (s : ℝ) : FiniteCramer.objective mu X ((n : ℝ)*rho) s =
      fullObjective n rho h pi s := by
    simp only [mu, X, FiniteCramer.objective, contactLaw_cgf, card_selected le_rfl,
      commonRate_fullMGF_eq hmass, fullObjective]
  obtain ⟨t, ht, hm, hr⟩ := FiniteCramer.optimizer hi
  have hr' : FiniteCramer.rate mu X ((n : ℝ)*rho) = fullRate n rho h pi := by
    unfold FiniteCramer.rate fullRate
    simp only [hrewrite]
  have hp := FiniteCramer.rate_pos hi
  rw [hr'] at hp hr
  refine ⟨hp, t, ht, ?_, ?_, ?_⟩
  · exact (hrewrite t).symm.trans hr.symm
  · intro s _
    rw [hr, ← hrewrite]
    exact FiniteCramer.objective_le_at_mean mu X hm s
  · intro s _ hs
    apply commonRate_optimizer_unique hi hm
    rw [hrewrite, hs, hr]

end FCAppendix.Ample

namespace FCAppendix.Bayes
open MeasureTheory Game Filter Topology Set Real
open Ample
open scoped BigOperators

namespace HasPopulationRate

theorem along {M : ℕ → ℕ} {p : ℕ → ℝ} {J : ℝ}
    (h : HasPopulationRate M p J) (phi : ℕ → ℕ) (hphi : Tendsto phi atTop atTop) :
    HasPopulationRate (M ∘ phi) (p ∘ phi) J :=
  ⟨hphi.eventually h.1, h.2.comp hphi⟩

theorem congr {M : ℕ → ℕ} {p q : ℕ → ℝ} {J : ℝ}
    (h : HasPopulationRate M p J) (hpq : p =ᶠ[atTop] q) : HasPopulationRate M q J := by
  refine ⟨?_, h.2.congr' (hpq.mono fun t ht => congrArg (populationLogRate (M t)) ht)⟩
  filter_upwards [h.1, hpq] with t ht he
  simpa only [← he] using ht

theorem const_mul {M : ℕ → ℕ} {p : ℕ → ℝ} {J a : ℝ}
    (h : HasPopulationRate M p J) (hM : Tendsto M atTop atTop) (ha : 0 < a) :
    HasPopulationRate M (fun t => a*p t) J := by
  have hi : Tendsto (fun t => (M t : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp hM)
  have hz : Tendsto (fun t => log a/(M t : ℝ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using hi.const_mul (log a)
  refine ⟨h.1.mono fun t ht => mul_pos ha ht, ?_⟩
  have ht := h.2.sub hz
  simp only [sub_zero] at ht
  apply ht.congr'
  filter_upwards [h.1] with t hp
  exact (populationLogRate_mul (M t) ha hp).symm

theorem rival_pow_mul {M : ℕ → ℕ} {p : ℕ → ℝ} {J a : ℝ}
    (h : HasPopulationRate M p J) (hM : Tendsto M atTop atTop) (ha : 0 < a) :
    HasPopulationRate M (fun t => a^(M t-1)*p t) (J-log a) := by
  have hc := (rival_fraction_tendsto_one M hM).mul_const (log a)
  simp only [one_mul] at hc
  refine ⟨h.1.mono fun t ht => mul_pos (pow_pos ha _) ht, ?_⟩
  apply (h.2.sub hc).congr'
  filter_upwards [h.1] with t hp
  unfold populationLogRate
  rw [log_mul (pow_ne_zero _ ha.ne') hp.ne', log_pow]
  ring

theorem eventually_lower_exp {M : ℕ → ℕ} {p : ℕ → ℝ} {J R : ℝ}
    (h : HasPopulationRate M p J) (hM : Tendsto M atTop atTop) (hJR : J < R) :
    ∀ᶠ t in atTop, exp (-(M t : ℝ)*R) ≤ p t := by
  filter_upwards [h.1, h.2.eventually_lt_const hJR, hM.eventually_gt_atTop 0]
    with t hp hr hm
  have hmR : (0 : ℝ) < M t := Nat.cast_pos.mpr hm
  have hh := (div_lt_iff₀ hmR).mp hr
  rw [← exp_log hp]
  apply exp_le_exp.mpr
  linarith

end HasPopulationRate

theorem commonRate_no_exponent_cross {M : ℕ → ℕ} {p q : ℕ → ℝ}
    (hM : Tendsto M atTop atTop) {L U : ℝ} (hLU : L < U)
    (hb : ∀ᶠ t in atTop, exp (-(M t : ℝ)*L) ≤ p t ∧ p t ≤ q t ∧
      q t ≤ exp (-(M t : ℝ)*U)) : False := by
  obtain ⟨t, ht, hm⟩ := (hb.and (hM.eventually_gt_atTop 0)).exists
  have hle := ht.1.trans (ht.2.1.trans ht.2.2)
  have hlt : exp (-(M t : ℝ)*U) < exp (-(M t : ℝ)*L) := by
    apply exp_lt_exp.mpr
    nlinarith [(Nat.cast_pos.mpr hm : (0 : ℝ) < M t)]
  exact (not_lt_of_ge hle) hlt

theorem commonRate_log_sandwich {M : ℕ → ℕ} {p r : ℕ → ℝ} {J w : ℝ}
    (hM : Tendsto M atTop atTop) (hw : 0 < w) (hr : HasPopulationRate M r J)
    (hupper : ∀ᶠ t in atTop, p t ≤ w*r t)
    (hlower : ∀ e > 0, ∀ᶠ t in atTop, exp (-(M t : ℝ)*(J+e)) ≤ p t) :
    HasPopulationRate M p J := by
  have hp : ∀ᶠ t in atTop, 0 < p t :=
    (hlower 1 (by norm_num)).mono fun t ht => (exp_pos _).trans_le ht
  refine ⟨hp, tendsto_order.mpr ⟨?_, ?_⟩⟩
  · intro l hl
    have hm := hr.const_mul hM hw
    filter_upwards [hp, hupper, hm.2.eventually_const_lt hl,
      hM.eventually_gt_atTop 0] with t hpt hut hlt hmt
    exact hlt.trans_le (populationLogRate_anti hmt hpt hut)
  · intro u hu
    let e := (u-J)/2
    have he : 0 < e := by dsimp [e]; linarith
    filter_upwards [hlower e he, hM.eventually_gt_atTop 0] with t ht hmt
    have hb := populationLogRate_anti hmt (exp_pos (-(M t : ℝ)*(J+e))) ht
    have hz : (M t : ℝ) ≠ 0 := (Nat.cast_pos.mpr hmt).ne'
    have heq : populationLogRate (M t) (exp (-(M t : ℝ)*(J+e))) = J+e := by
      unfold populationLogRate
      rw [log_exp]
      field_simp [hz]
    rw [heq] at hb
    exact hb.trans_lt (by dsimp [e]; linarith)

theorem commonRate_compact_log {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    {M C : ℕ → ℕ} (Γ : ∀ t, FiniteGame (M t) n (C t) Seed)
    (hM : Tendsto M atTop atTop) {lo hi J : ℝ} (hlo : 0 < lo) (hlh : lo ≤ hi)
    (hr : HasPopulationRate M (fun t => actualDeficit (Γ t) lo) J) :
    ∀ e > 0, ∀ᶠ t in atTop, ∀ w ∈ Icc lo hi,
      |populationLogRate (M t) (actualDeficit (Γ t) w)-J| < e := by
  have hratio : 0 < hi/lo := div_pos (hlo.trans_le hlh) hlo
  have hscaled := hr.const_mul hM hratio
  intro e he
  filter_upwards [hr.1, hr.2.eventually_lt_const (show J < J+e by linarith),
    hscaled.2.eventually_const_lt (show J-e < J by linarith),
    hM.eventually_gt_atTop 0] with t hpos hright hleft hm
  intro w hw
  have hw0 : 0 < w := hlo.trans_le hw.1
  have cmp := actualDeficit_ratio_bounds (Γ t) hm w lo hw0 hlo
  have hwl : 1 ≤ w/lo := (le_div_iff₀ hlo).mpr (by simpa using hw.1)
  rw [min_eq_left hwl, max_eq_right hwl, one_mul] at cmp
  have hwpos := hpos.trans_le cmp.1
  have hwh : w/lo*actualDeficit (Γ t) lo ≤ hi/lo*actualDeficit (Γ t) lo :=
    mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hw.2 hlo.le) hpos.le
  have hl := populationLogRate_anti hm hwpos (cmp.2.trans hwh)
  have hu := populationLogRate_anti hm hpos cmp.1
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

end FCAppendix.Bayes
