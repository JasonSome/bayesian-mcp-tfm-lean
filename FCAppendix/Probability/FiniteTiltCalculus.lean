import FCAppendix.Probability.SimultaneousCongestion
import Mathlib.Analysis.Convex.Deriv

namespace FCAppendix.FiniteCramer

open Filter Topology Set Real
open scoped BigOperators
open SimultaneousCongestion

variable {Ω : Type*} [Fintype Ω]

noncomputable def Z (μ : FiniteLaw Ω) (X : Ω → ℝ) (t : ℝ) : ℝ :=
  μ.expect (fun x => exp (t * X x))

noncomputable def cgf (μ : FiniteLaw Ω) (X : Ω → ℝ) (t : ℝ) : ℝ :=
  log (Z μ X t)

noncomputable def tilted (μ : FiniteLaw Ω) (X : Ω → ℝ) (t : ℝ) : FiniteLaw Ω :=
  tilt μ (fun x => t * X x)

noncomputable def mean (μ : FiniteLaw Ω) (X : Ω → ℝ) (t : ℝ) : ℝ :=
  (tilted μ X t).expect X

noncomputable def variance (ν : FiniteLaw Ω) (X : Ω → ℝ) : ℝ :=
  ν.expect (fun x => (X x - ν.expect X) ^ 2)

noncomputable def objective (μ : FiniteLaw Ω) (X : Ω → ℝ) (r t : ℝ) : ℝ :=
  r * t - cgf μ X t

noncomputable def rate (μ : FiniteLaw Ω) (X : Ω → ℝ) (r : ℝ) : ℝ :=
  ⨆ t : Ici (0 : ℝ), objective μ X r t

def Interior (μ : FiniteLaw Ω) (X : Ω → ℝ) (r : ℝ) : Prop :=
  μ.expect X < r ∧ ∃ x, 0 < μ.mass x ∧ r < X x

theorem Z_pos (μ : FiniteLaw Ω) (X : Ω → ℝ) (t : ℝ) : 0 < Z μ X t :=
  expect_pos μ (fun _ => exp_pos _)

@[simp] theorem Z_zero (μ : FiniteLaw Ω) (X : Ω → ℝ) : Z μ X 0 = 1 := by
  simp [Z]

@[simp] theorem cgf_zero (μ : FiniteLaw Ω) (X : Ω → ℝ) : cgf μ X 0 = 0 := by
  simp [cgf]

@[simp] theorem objective_zero (μ : FiniteLaw Ω) (X : Ω → ℝ) (r : ℝ) :
    objective μ X r 0 = 0 := by simp [objective]

theorem mean_eq (μ : FiniteLaw Ω) (X : Ω → ℝ) (t : ℝ) :
    mean μ X t = μ.expect (fun x => X x * exp (t * X x)) / Z μ X t := by
  exact expect_tilt μ (fun x => t * X x) X

@[simp] theorem mean_zero (μ : FiniteLaw Ω) (X : Ω → ℝ) :
    mean μ X 0 = μ.expect X := by
  rw [mean_eq]
  simp

theorem variance_eq (ν : FiniteLaw Ω) (X : Ω → ℝ) :
    variance ν X = ν.expect (fun x => X x ^ 2) - (ν.expect X) ^ 2 := by
  unfold variance
  calc
    _ = ν.expect (fun x => X x ^ 2 - (2 * ν.expect X) * X x + (ν.expect X) ^ 2) :=
      ν.expect_congr (fun _ => by ring)
    _ = _ := by
      rw [ν.expect_add, ν.expect_sub, ν.expect_const_mul, ν.expect_const]
      ring

theorem variance_nonneg (ν : FiniteLaw Ω) (X : Ω → ℝ) : 0 ≤ variance ν X :=
  ν.expect_nonneg (fun _ => sq_nonneg _)

theorem hasDerivAt_weightedExp (μ : FiniteLaw Ω) (X f : Ω → ℝ) (t : ℝ) :
    HasDerivAt (fun u => μ.expect (fun x => f x * exp (u * X x)))
      (μ.expect (fun x => f x * X x * exp (t * X x))) t := by
  classical
  unfold FiniteLaw.expect
  have h (x : Ω) :
      HasDerivAt (fun u => μ.mass x * (f x * exp (u * X x)))
        (μ.mass x * (f x * X x * exp (t * X x))) t := by
    have h := ((((hasDerivAt_id t).mul_const (X x)).exp).const_mul (f x)).const_mul
      (μ.mass x)
    simpa only [id_eq, one_mul, mul_assoc, mul_comm, mul_left_comm] using h
  exact HasDerivAt.fun_sum (fun x _ => h x)

theorem hasDerivAt_Z (μ : FiniteLaw Ω) (X : Ω → ℝ) (t : ℝ) :
    HasDerivAt (Z μ X) (μ.expect (fun x => X x * exp (t * X x))) t := by
  change HasDerivAt (fun u => μ.expect (fun x => exp (u * X x))) _ t
  simpa only [one_mul] using hasDerivAt_weightedExp μ X (fun _ => 1) t

theorem hasDerivAt_cgf (μ : FiniteLaw Ω) (X : Ω → ℝ) (t : ℝ) :
    HasDerivAt (cgf μ X) (mean μ X t) t := by
  rw [mean_eq]
  exact (hasDerivAt_Z μ X t).log (Z_pos μ X t).ne'

@[simp] theorem deriv_cgf (μ : FiniteLaw Ω) (X : Ω → ℝ) (t : ℝ) :
    deriv (cgf μ X) t = mean μ X t :=
  (hasDerivAt_cgf μ X t).deriv

theorem hasDerivAt_mean (μ : FiniteLaw Ω) (X : Ω → ℝ) (t : ℝ) :
    HasDerivAt (mean μ X) (variance (tilted μ X t) X) t := by
  have hZ := (Z_pos μ X t).ne'
  have h := (hasDerivAt_weightedExp μ X X t).div (hasDerivAt_Z μ X t) hZ
  have hv : variance (tilted μ X t) X =
      (μ.expect (fun x => X x * X x * exp (t * X x)) * Z μ X t -
        μ.expect (fun x => X x * exp (t * X x)) *
          μ.expect (fun x => X x * exp (t * X x))) / (Z μ X t) ^ 2 := by
    rw [variance_eq]
    change (tilt μ (fun x => t * X x)).expect (fun x => X x ^ 2) -
      (mean μ X t) ^ 2 = _
    rw [expect_tilt, mean_eq]
    change μ.expect (fun x => X x ^ 2 * exp (t * X x)) / Z μ X t - _ = _
    simp only [pow_two]
    field_simp [hZ]
    simp only [mul_comm]
  rw [hv]
  apply h.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun u => mean_eq μ X u)

@[simp] theorem deriv_mean (μ : FiniteLaw Ω) (X : Ω → ℝ) (t : ℝ) :
    deriv (mean μ X) t = variance (tilted μ X t) X :=
  (hasDerivAt_mean μ X t).deriv

theorem differentiable_cgf (μ : FiniteLaw Ω) (X : Ω → ℝ) :
    Differentiable ℝ (cgf μ X) := fun t => (hasDerivAt_cgf μ X t).differentiableAt

theorem differentiable_mean (μ : FiniteLaw Ω) (X : Ω → ℝ) :
    Differentiable ℝ (mean μ X) := fun t => (hasDerivAt_mean μ X t).differentiableAt

theorem convex_cgf (μ : FiniteLaw Ω) (X : Ω → ℝ) : ConvexOn ℝ univ (cgf μ X) := by
  apply convexOn_univ_of_deriv2_nonneg (differentiable_cgf μ X)
  · rw [show deriv (cgf μ X) = mean μ X from funext (deriv_cgf μ X)]
    exact differentiable_mean μ X
  · intro t
    change 0 ≤ deriv (deriv (cgf μ X)) t
    rw [show deriv (cgf μ X) = mean μ X from funext (deriv_cgf μ X), deriv_mean]
    exact variance_nonneg _ _

theorem Interior.nonconstant {μ : FiniteLaw Ω} {X : Ω → ℝ} {r : ℝ}
    (h : Interior μ X r) (a : ℝ) : ∃ x, 0 < μ.mass x ∧ X x ≠ a := by
  classical
  by_contra hn
  have hc : ∀ x, 0 < μ.mass x → X x = a := by
    simpa only [not_exists, not_and, not_not] using hn
  have hE : μ.expect X = a := by
    calc
      _ = μ.expect (fun _ => a) := by
        unfold FiniteLaw.expect
        apply Finset.sum_congr rfl
        intro x _
        by_cases hx : μ.mass x = 0
        · simp [hx]
        · rw [hc x (lt_of_le_of_ne (μ.nonneg x) (Ne.symm hx))]
      _ = a := μ.expect_const a
  obtain ⟨x, hx, hxr⟩ := h.2
  rw [hc x hx] at hxr
  linarith [h.1]

theorem variance_tilt_pos {μ : FiniteLaw Ω} {X : Ω → ℝ} {r : ℝ}
    (h : Interior μ X r) (t : ℝ) : 0 < variance (tilted μ X t) X := by
  classical
  obtain ⟨x, hx, hne⟩ := h.nonconstant (mean μ X t)
  have hmass : 0 < (tilted μ X t).mass x :=
    div_pos (mul_pos hx (exp_pos _)) (Z_pos μ X t)
  unfold variance FiniteLaw.expect
  apply Finset.sum_pos'
  · intro y _
    exact mul_nonneg ((tilted μ X t).nonneg y) (sq_nonneg _)
  · refine ⟨x, Finset.mem_univ _, mul_pos hmass ?_⟩
    exact sq_pos_of_ne_zero (sub_ne_zero.mpr hne)

theorem strictMono_mean {μ : FiniteLaw Ω} {X : Ω → ℝ} {r : ℝ}
    (h : Interior μ X r) : StrictMono (mean μ X) := by
  apply strictMono_of_deriv_pos
  intro t
  rw [deriv_mean]
  exact variance_tilt_pos h t

theorem cgf_ge_atom (μ : FiniteLaw Ω) (X : Ω → ℝ) (t : ℝ) {x : Ω}
    (hx : 0 < μ.mass x) : log (μ.mass x) + t * X x ≤ cgf μ X t := by
  have hb : μ.mass x * exp (t * X x) ≤ Z μ X t := by
    unfold Z FiniteLaw.expect
    exact Finset.single_le_sum (f := fun y => μ.mass y * exp (t * X y))
      (fun y _ => mul_nonneg (μ.nonneg y) (exp_pos _).le) (Finset.mem_univ x)
  have hh := log_le_log (mul_pos hx (exp_pos _)) hb
  simpa only [log_mul hx.ne' (exp_ne_zero _), log_exp, cgf] using hh

theorem exists_mean_gt {μ : FiniteLaw Ω} {X : Ω → ℝ} {r : ℝ}
    (h : Interior μ X r) : ∃ T, 0 < T ∧ r < mean μ X T := by
  obtain ⟨x, hx, hxr⟩ := h.2
  let v : ℝ := (|log (μ.mass x)| + 1) / (X x - r)
  have hv : 0 < v := div_pos (by positivity) (sub_pos.mpr hxr)
  have hprod : v * (X x - r) = |log (μ.mass x)| + 1 :=
    div_mul_cancel₀ _ (sub_ne_zero.mpr hxr.ne')
  let f : ℝ → ℝ := fun t => cgf μ X t - r * t
  have hf : Differentiable ℝ f :=
    (differentiable_cgf μ X).sub (differentiable_id.const_mul r)
  have hf0 : f 0 = 0 := by simp [f]
  have hfv : 0 < f v := by
    have hb := cgf_ge_atom μ X v hx
    have habs := neg_le_abs (log (μ.mass x))
    dsimp [f]
    nlinarith
  obtain ⟨w, hw, hd⟩ := exists_deriv_eq_slope f hv hf.continuous.continuousOn
    hf.differentiableOn
  have he : deriv f w = mean μ X w - r := by
    have hh := (hasDerivAt_cgf μ X w).sub ((hasDerivAt_id w).const_mul r)
    have hh' : HasDerivAt f (mean μ X w - r * 1) w :=
      hh.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun _ => rfl))
    simpa only [mul_one] using hh'.deriv
  rw [he, hf0] at hd
  refine ⟨w, hw.1, ?_⟩
  have hs : 0 < (f v - 0) / (v - 0) := div_pos (by linarith) (by linarith)
  linarith

theorem exists_unique_optimizer_mean {μ : FiniteLaw Ω} {X : Ω → ℝ} {r : ℝ}
    (h : Interior μ X r) : ∃! t : ℝ, 0 < t ∧ mean μ X t = r := by
  obtain ⟨T, hT, hTm⟩ := exists_mean_gt h
  obtain ⟨t, ht, htr⟩ := intermediate_value_Icc hT.le
    (differentiable_mean μ X).continuous.continuousOn
    (show r ∈ Icc (mean μ X 0) (mean μ X T) by simpa using ⟨h.1.le, hTm.le⟩)
  have ht0 : 0 < t := by
    by_contra hn
    have hz : t = 0 := le_antisymm (not_lt.mp hn) ht.1
    rw [hz, mean_zero] at htr
    linarith [h.1]
  refine ⟨t, ⟨ht0, htr⟩, ?_⟩
  intro u hu
  exact (strictMono_mean h).injective (hu.2.trans htr.symm)

theorem objective_le_at_mean (μ : FiniteLaw Ω) (X : Ω → ℝ) {r t : ℝ}
    (ht : mean μ X t = r) (u : ℝ) : objective μ X r u ≤ objective μ X r t := by
  rcases lt_trichotomy u t with hu | rfl | hu
  · have hh := (convex_cgf μ X).slope_le_deriv (mem_univ u) (mem_univ t) hu
      (differentiable_cgf μ X t)
    rw [deriv_cgf, ht, slope_def_field] at hh
    have he := (div_le_iff₀ (sub_pos.mpr hu)).mp hh
    dsimp [objective]
    nlinarith
  · rfl
  · have hh := (convex_cgf μ X).deriv_le_slope (mem_univ t) (mem_univ u) hu
      (differentiable_cgf μ X t)
    rw [deriv_cgf, ht, slope_def_field] at hh
    have he := (le_div_iff₀ (sub_pos.mpr hu)).mp hh
    dsimp [objective]
    nlinarith

theorem rate_eq_at_mean (μ : FiniteLaw Ω) (X : Ω → ℝ) {r t : ℝ}
    (ht0 : 0 ≤ t) (ht : mean μ X t = r) : rate μ X r = objective μ X r t := by
  have hb : BddAbove (Set.range fun u : Ici (0 : ℝ) => objective μ X r u) := by
    refine ⟨objective μ X r t, ?_⟩
    rintro _ ⟨u, rfl⟩
    exact objective_le_at_mean μ X ht u
  apply le_antisymm
  · exact ciSup_le fun u => objective_le_at_mean μ X ht u
  · exact le_ciSup hb ⟨t, ht0⟩

theorem optimizer {μ : FiniteLaw Ω} {X : Ω → ℝ} {r : ℝ} (h : Interior μ X r) :
    ∃ t, 0 < t ∧ mean μ X t = r ∧ rate μ X r = objective μ X r t := by
  obtain ⟨t, ht, _⟩ := exists_unique_optimizer_mean h
  exact ⟨t, ht.1, ht.2, rate_eq_at_mean μ X ht.1.le ht.2⟩

theorem rate_pos {μ : FiniteLaw Ω} {X : Ω → ℝ} {r : ℝ} (h : Interior μ X r) :
    0 < rate μ X r := by
  obtain ⟨t, ht, hm, hr⟩ := optimizer h
  have hd (u : ℝ) : HasDerivAt (objective μ X r) (r - mean μ X u) u := by
    have hh := ((hasDerivAt_id u).const_mul r).sub (hasDerivAt_cgf μ X u)
    have hh' : HasDerivAt (objective μ X r) (r * 1 - mean μ X u) u :=
      hh.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun _ => rfl))
    simpa only [mul_one] using hh'
  have hstrict : StrictMonoOn (objective μ X r) (Icc 0 t) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 t)
    · exact (continuous_iff_continuousAt.mpr (fun u => (hd u).continuousAt)).continuousOn
    · intro u hu
      rw [(hd u).deriv]
      have hut : u < t := (show u ∈ Ioo 0 t from by simpa only [interior_Icc] using hu).2
      have hmu := strictMono_mean h hut
      linarith
  rw [hr]
  simpa only [objective_zero] using
    hstrict ⟨le_rfl, ht.le⟩ ⟨ht.le, le_rfl⟩ ht

theorem exists_tilt_lower_bound {μ : FiniteLaw Ω} {X : Ω → ℝ} {r a : ℝ}
    (h : Interior μ X r) (ha : a < -rate μ X r) :
    ∃ t, 0 ≤ t ∧ r < mean μ X t ∧ a < cgf μ X t - t * mean μ X t := by
  obtain ⟨t, ht, htm, hr⟩ := optimizer h
  let u : ℕ → ℝ := fun j => t + 1 / ((j : ℝ) + 1)
  have hulim : Tendsto u atTop (𝓝 t) := by
    simpa [u] using tendsto_one_div_add_atTop_nhds_zero_nat.const_add t
  have hc := (differentiable_cgf μ X).continuous.continuousAt.tendsto.comp hulim
  have hm := (differentiable_mean μ X).continuous.continuousAt.tendsto.comp hulim
  have he := hc.sub (hulim.mul hm)
  have hval : cgf μ X t - t * mean μ X t = -rate μ X r := by
    rw [htm, hr]
    dsimp [objective]
    ring
  rw [hval] at he
  obtain ⟨j, hj⟩ := (he.eventually_const_lt ha).exists
  have htu : t < u j := lt_add_of_pos_right _ (by positivity)
  refine ⟨u j, (ht.trans htu).le, ?_, hj⟩
  rw [← htm]
  exact strictMono_mean h htu

theorem tendsto_Z {A : Type*} {l : Filter A} {μa : A → FiniteLaw Ω} {μ : FiniteLaw Ω}
    (hμ : ∀ x, Tendsto (fun a => (μa a).mass x) l (𝓝 (μ.mass x)))
    (X : Ω → ℝ) {ta : A → ℝ} {t : ℝ} (ht : Tendsto ta l (𝓝 t)) :
    Tendsto (fun a => Z (μa a) X (ta a)) l (𝓝 (Z μ X t)) := by
  unfold Z FiniteLaw.expect
  exact tendsto_finsetSum Finset.univ (fun x _ => (hμ x).mul (Real.continuous_exp.continuousAt.tendsto.comp (ht.mul_const (X x))))

theorem tendsto_cgf {A : Type*} {l : Filter A} {μa : A → FiniteLaw Ω} {μ : FiniteLaw Ω}
    (hμ : ∀ x, Tendsto (fun a => (μa a).mass x) l (𝓝 (μ.mass x)))
    (X : Ω → ℝ) {ta : A → ℝ} {t : ℝ} (ht : Tendsto ta l (𝓝 t)) :
    Tendsto (fun a => cgf (μa a) X (ta a)) l (𝓝 (cgf μ X t)) :=
  (tendsto_Z hμ X ht).log (Z_pos μ X t).ne'

theorem tendsto_mean {A : Type*} {l : Filter A} {μa : A → FiniteLaw Ω} {μ : FiniteLaw Ω}
    (hμ : ∀ x, Tendsto (fun a => (μa a).mass x) l (𝓝 (μ.mass x)))
    (X : Ω → ℝ) {ta : A → ℝ} {t : ℝ} (ht : Tendsto ta l (𝓝 t)) :
    Tendsto (fun a => mean (μa a) X (ta a)) l (𝓝 (mean μ X t)) := by
  simp_rw [mean_eq]
  apply Tendsto.div _ (tendsto_Z hμ X ht) (Z_pos μ X t).ne'
  unfold FiniteLaw.expect
  exact tendsto_finsetSum Finset.univ (fun x _ =>
    (hμ x).mul ((Real.continuous_exp.continuousAt.tendsto.comp (ht.mul_const (X x))).const_mul (X x)))

theorem tendsto_expect {A : Type*} {l : Filter A} {μa : A → FiniteLaw Ω} {μ : FiniteLaw Ω}
    (hμ : ∀ x, Tendsto (fun a => (μa a).mass x) l (𝓝 (μ.mass x))) (X : Ω → ℝ) :
    Tendsto (fun a => (μa a).expect X) l (𝓝 (μ.expect X)) := by
  unfold FiniteLaw.expect
  exact tendsto_finsetSum Finset.univ (fun x _ => (hμ x).mul_const (X x))

theorem eventually_interior {A : Type*} {l : Filter A}
    {μa : A → FiniteLaw Ω} {μ : FiniteLaw Ω} {X : Ω → ℝ} {ra : A → ℝ} {r : ℝ}
    (hμ : ∀ x, Tendsto (fun a => (μa a).mass x) l (𝓝 (μ.mass x)))
    (hr : Tendsto ra l (𝓝 r)) (h : Interior μ X r) :
    ∀ᶠ a in l, Interior (μa a) X (ra a) := by
  obtain ⟨x, hx, hxr⟩ := h.2
  have hm := (hr.sub (tendsto_expect hμ X)).eventually_const_lt
    (show 0 < r - μ.expect X by linarith [h.1])
  filter_upwards [hm, (hμ x).eventually_const_lt hx, hr.eventually_lt_const hxr]
    with a ha hp htop
  exact ⟨by linarith, x, hp, htop⟩

theorem tendsto_rate {A : Type*} {l : Filter A}
    {μa : A → FiniteLaw Ω} {μ : FiniteLaw Ω} {X : Ω → ℝ} {ra : A → ℝ} {r : ℝ}
    (hμ : ∀ x, Tendsto (fun a => (μa a).mass x) l (𝓝 (μ.mass x)))
    (hr : Tendsto ra l (𝓝 r)) (h : Interior μ X r) :
    Tendsto (fun a => rate (μa a) X (ra a)) l (𝓝 (rate μ X r)) := by
  classical
  obtain ⟨t, ht, htm, htr⟩ := optimizer h
  let u (a : A) : ℝ := if ha : Interior (μa a) X (ra a) then
    Classical.choose (optimizer ha) else 0
  have hint := eventually_interior hμ hr h
  have hu : ∀ᶠ a in l, Interior (μa a) X (ra a) ∧ 0 < u a ∧
      mean (μa a) X (u a) = ra a ∧
      rate (μa a) X (ra a) = objective (μa a) X (ra a) (u a) := by
    filter_upwards [hint] with a ha
    refine ⟨ha, ?_⟩
    simpa only [u, dif_pos ha] using Classical.choose_spec (optimizer ha)
  have hulim : Tendsto u l (𝓝 t) := by
    apply tendsto_order.mpr
    constructor
    · intro v hv
      have hvmean : mean μ X v < r := by rw [← htm]; exact strictMono_mean h hv
      have hgap := hr.sub (tendsto_mean hμ X (t := v) tendsto_const_nhds)
      filter_upwards [hu, hgap.eventually_const_lt (show 0 < r - mean μ X v by linarith)]
        with a ha hb
      apply (strictMono_mean ha.1).lt_iff_lt.mp
      rw [ha.2.2.1]
      linarith
    · intro v hv
      have hvmean : r < mean μ X v := by rw [← htm]; exact strictMono_mean h hv
      have hgap := (tendsto_mean hμ X (t := v) tendsto_const_nhds).sub hr
      filter_upwards [hu, hgap.eventually_const_lt (show 0 < mean μ X v - r by linarith)]
        with a ha hb
      apply (strictMono_mean ha.1).lt_iff_lt.mp
      rw [ha.2.2.1]
      linarith
  have hv := (hr.mul hulim).sub (tendsto_cgf hμ X hulim)
  have heq : (fun a => ra a * u a - cgf (μa a) X (u a)) =ᶠ[l]
      (fun a => rate (μa a) X (ra a)) :=
    hu.mono (fun _ ha => ha.2.2.2.symm)
  rw [htr]
  exact hv.congr' heq

end FCAppendix.FiniteCramer
