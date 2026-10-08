import FCAppendix.Finite.Envelope

namespace FCAppendix

open MeasureTheory Set Filter Topology

namespace Subgradient

theorem ordered {f : ℝ → ℝ} {u v a b : ℝ} (huv : u < v)
    (ha : f u + (v - u) * a ≤ f v) (hb : f v + (u - v) * b ≤ f u) : a ≤ b := by
  by_contra h
  have hp := mul_pos (sub_pos.mpr huv) (sub_pos.mpr (lt_of_not_ge h))
  nlinarith

theorem monotoneOn {f s : ℝ → ℝ} {S : Set ℝ}
    (hs : ∀ v ∈ S, ∀ w ∈ S, f v + (w - v) * s v ≤ f w) : MonotoneOn s S := by
  intro u hu v hv huv
  rcases eq_or_lt_of_le huv with rfl | h
  · exact le_rfl
  · exact ordered h (hs u hu v hv) (hs v hv u hu)

theorem intervalIntegrable {f s : ℝ → ℝ} {x y a b : ℝ}
    (hs : ∀ v ∈ Icc x y, ∀ w ∈ Icc x y, f v + (w - v) * s v ≤ f w)
    (ha : a ∈ Icc x y) (hb : b ∈ Icc x y) : IntervalIntegrable s volume a b :=
  ((monotoneOn hs).mono (uIcc_subset_Icc ha hb)).intervalIntegrable

theorem abs_increment_sub_integral_le {f s : ℝ → ℝ} {x y a b : ℝ}
    (hs : ∀ v ∈ Icc x y, ∀ w ∈ Icc x y, f v + (w - v) * s v ≤ f w)
    (ha : a ∈ Icc x y) (hb : b ∈ Icc x y) (hab : a ≤ b) :
    |f b - f a - ∫ v in a..b, s v| ≤ (b - a) * (s b - s a) := by
  have hmono := monotoneOn hs
  have hsub : Icc a b ⊆ Icc x y := Icc_subset_Icc ha.1 hb.2
  have hint := intervalIntegrable hs ha hb
  have hlo : (b - a) * s a ≤ ∫ v in a..b, s v := by
    have h := intervalIntegral.integral_mono_on hab intervalIntegrable_const hint
      (fun v hv => hmono ha (hsub hv) hv.1)
    simpa only [intervalIntegral.integral_const, smul_eq_mul] using h
  have hhi : ∫ v in a..b, s v ≤ (b - a) * s b := by
    have h := intervalIntegral.integral_mono_on hab hint intervalIntegrable_const
      (fun v hv => hmono (hsub hv) hb hv.2)
    simpa only [intervalIntegral.integral_const, smul_eq_mul] using h
  have h1 := hs a ha b hb
  have h2 := hs b hb a ha
  rw [abs_le]
  constructor <;> nlinarith

theorem sub_eq_integral {f s : ℝ → ℝ} {x y : ℝ} (hxy : x ≤ y)
    (hs : ∀ v ∈ Icc x y, ∀ w ∈ Icc x y, f v + (w - v) * s v ≤ f w) :
    f y - f x = ∫ v in x..y, s v := by
  set D := f y - f x - ∫ v in x..y, s v with hD
  set C := (y - x) * (s y - s x) with hC

  have hbound : ∀ N : ℕ, 1 ≤ N → |D| ≤ C / N := by
    intro N hN
    have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
    set h := (y - x) / N with hh
    have hh0 : 0 ≤ h := div_nonneg (sub_nonneg.mpr hxy) hNr.le
    have hNh : (N : ℝ) * h = y - x := by rw [hh]; field_simp
    set t : ℕ → ℝ := fun i => x + i * h with ht
    have ht0 : t 0 = x := by simp [ht]
    have htN : t N = y := by simp only [ht]; rw [hNh]; ring
    have hstep : ∀ i : ℕ, t (i + 1) - t i = h := by
      intro i; simp only [ht]; push_cast; ring
    have hmem : ∀ i : ℕ, i ≤ N → t i ∈ Icc x y := by
      intro i hi
      have hi' : (i : ℝ) * h ≤ N * h :=
        mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hi) hh0
      constructor
      · simp only [ht]; nlinarith [mul_nonneg (Nat.cast_nonneg i : (0 : ℝ) ≤ i) hh0]
      · simp only [ht]; linarith
    have hint : ∀ i < N, IntervalIntegrable s volume (t i) (t (i + 1)) := fun i hi =>
      intervalIntegrable hs (hmem i hi.le) (hmem (i + 1) hi)
    have hsumI := intervalIntegral.sum_integral_adjacent_intervals hint
    have hsumF : ∑ i ∈ Finset.range N, (f (t (i + 1)) - f (t i)) = f (t N) - f (t 0) :=
      Finset.sum_range_sub (fun i => f (t i)) N
    have hsumS : ∑ i ∈ Finset.range N, (s (t (i + 1)) - s (t i)) = s (t N) - s (t 0) :=
      Finset.sum_range_sub (fun i => s (t i)) N
    have hDsum : D = ∑ i ∈ Finset.range N,
        (f (t (i + 1)) - f (t i) - ∫ v in t i..t (i + 1), s v) := by
      rw [Finset.sum_sub_distrib, hsumF, hsumI, ht0, htN]
    calc |D| ≤ ∑ i ∈ Finset.range N,
          |f (t (i + 1)) - f (t i) - ∫ v in t i..t (i + 1), s v| := by
            rw [hDsum]; exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.range N, h * (s (t (i + 1)) - s (t i)) := by
            apply Finset.sum_le_sum
            intro i hi
            have hi' := Finset.mem_range.mp hi
            have hle : t i ≤ t (i + 1) := by linarith [hstep i]
            have hcell := abs_increment_sub_integral_le hs (hmem i hi'.le) (hmem (i + 1) hi') hle
            rwa [hstep i] at hcell
      _ = h * (s y - s x) := by rw [← Finset.mul_sum, hsumS, htN, ht0]
      _ = C / N := by rw [hh, hC]; ring

  have hlim : Tendsto (fun N : ℕ => C / (N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat C
  have hD0 : |D| ≤ 0 := ge_of_tendsto hlim (eventually_atTop.mpr ⟨1, hbound⟩)
  have hDz : D = 0 := abs_nonpos_iff.mp hD0
  linarith

theorem sub_eq_integral_of_ae_eq {f s s' : ℝ → ℝ} {x y : ℝ} (hxy : x ≤ y)
    (hs : ∀ v ∈ Icc x y, ∀ w ∈ Icc x y, f v + (w - v) * s v ≤ f w)
    (hae : ∀ᵐ v, v ∈ Icc x y → s' v = s v) :
    f y - f x = ∫ v in x..y, s' v := by
  rw [sub_eq_integral hxy hs]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [hae] with v hv hvI
  rw [uIoc_of_le hxy] at hvI
  exact (hv (Ioc_subset_Icc_self hvI)).symm

theorem eq_of_continuousAt {f s : ℝ → ℝ} {x y v c : ℝ}
    (hs : ∀ u ∈ Icc x y, ∀ w ∈ Icc x y, f u + (w - u) * s u ≤ f w)
    (hv : v ∈ Ioo x y) (hc : ∀ w ∈ Icc x y, f v + (w - v) * c ≤ f w)
    (hcont : ContinuousAt s v) : c = s v := by
  have hvI : v ∈ Icc x y := Ioo_subset_Icc_self hv
  apply le_antisymm
  ·
    have ht : Tendsto s (𝓝[>] v) (𝓝 (s v)) := hcont.tendsto.mono_left nhdsWithin_le_nhds
    refine ge_of_tendsto ht ?_
    filter_upwards [Ioo_mem_nhdsGT hv.2] with w hw
    have hwI : w ∈ Icc x y := ⟨hv.1.le.trans hw.1.le, hw.2.le⟩
    exact ordered hw.1 (hc w hwI) (hs w hwI v hvI)
  ·
    have ht : Tendsto s (𝓝[<] v) (𝓝 (s v)) := hcont.tendsto.mono_left nhdsWithin_le_nhds
    refine le_of_tendsto ht ?_
    filter_upwards [Ioo_mem_nhdsLT hv.1] with u hu
    have huI : u ∈ Icc x y := ⟨hu.1.le, hu.2.le.trans hv.2.le⟩
    exact ordered hu.2 (hs u huI v hvI) (hc u huI)

theorem ae_eq_of_ae_subgradient {f s s' : ℝ → ℝ} {x y : ℝ}
    (hs : ∀ v ∈ Icc x y, ∀ w ∈ Icc x y, f v + (w - v) * s v ≤ f w)
    (hs' : ∀ᵐ v, v ∈ Icc x y → ∀ w ∈ Icc x y, f v + (w - v) * s' v ≤ f w) :
    ∀ᵐ v, v ∈ Icc x y → s' v = s v := by
  have hjump := (monotoneOn hs).countable_not_continuousWithinAt
  have hends : ({x, y} : Set ℝ).Countable := (Set.toFinite _).countable
  filter_upwards [hs', hjump.ae_notMem volume, hends.ae_notMem volume] with v h1 h2 h3 hv
  have hvx : v ≠ x := fun h => h3 (Or.inl h)
  have hvy : v ≠ y := fun h => h3 (Or.inr h)
  have hvo : v ∈ Ioo x y := ⟨lt_of_le_of_ne hv.1 (Ne.symm hvx), lt_of_le_of_ne hv.2 hvy⟩
  have hcont : ContinuousWithinAt s (Icc x y) v := by
    by_contra hnot
    exact h2 ⟨hv, hnot⟩
  exact eq_of_continuousAt hs hvo (h1 hv) (hcont.continuousAt (Icc_mem_nhds hvo.1 hvo.2))

theorem rightDeriv_subgradient {f : ℝ → ℝ} {S : Set ℝ} (hf : ConvexOn ℝ S f) {v w : ℝ}
    (hv : v ∈ interior S) (hw : w ∈ S) :
    f v + (w - v) * derivWithin f (Ioi v) v ≤ f w := by
  rcases lt_trichotomy v w with hvw | rfl | hwv
  · have h := hf.rightDeriv_le_slope_of_mem_interior hv hw hvw
    rw [slope_def_field, le_div_iff₀ (sub_pos.mpr hvw)] at h
    linarith
  · simp
  · have h := (hf.slope_le_leftDeriv_of_mem_interior hw hv hwv).trans
      (hf.leftDeriv_le_rightDeriv_of_mem_interior hv)
    rw [slope_def_field, div_le_iff₀ (sub_pos.mpr hwv)] at h
    linarith

theorem sub_eq_integral_of_ae_subgradient {f s' : ℝ → ℝ} {S : Set ℝ} {x y : ℝ}
    (hf : ConvexOn ℝ S f) (hS : Icc x y ⊆ interior S) (hxy : x ≤ y)
    (hs' : ∀ᵐ v, v ∈ Icc x y → ∀ w ∈ Icc x y, f v + (w - v) * s' v ≤ f w) :
    f y - f x = ∫ v in x..y, s' v := by
  have hs : ∀ v ∈ Icc x y, ∀ w ∈ Icc x y, f v + (w - v) * derivWithin f (Ioi v) v ≤ f w :=
    fun v hv w hw => rightDeriv_subgradient hf (hS hv) (interior_subset (hS hw))
  exact sub_eq_integral_of_ae_eq hxy hs (ae_eq_of_ae_subgradient hs hs')

theorem finset_average {ι : Type*} {f : ℝ → ℝ} {S : Set ℝ} {v : ℝ} (t : Finset ι)
    (p c : ι → ℝ) (hp : ∀ i ∈ t, 0 ≤ p i) (hsum : ∑ i ∈ t, p i = 1)
    (hc : ∀ i ∈ t, ∀ w ∈ S, f v + (w - v) * c i ≤ f w) :
    ∀ w ∈ S, f v + (w - v) * ∑ i ∈ t, p i * c i ≤ f w := by
  intro w hw
  have h : ∑ i ∈ t, p i * (f v + (w - v) * c i) ≤ ∑ i ∈ t, p i * f w :=
    Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hc i hi w hw) (hp i hi)
  have e1 : ∑ i ∈ t, p i * (f v + (w - v) * c i) = f v + (w - v) * ∑ i ∈ t, p i * c i := by
    calc ∑ i ∈ t, p i * (f v + (w - v) * c i)
        = ∑ i ∈ t, (p i * f v + (w - v) * (p i * c i)) :=
          Finset.sum_congr rfl fun i _ => by ring
      _ = (∑ i ∈ t, p i) * f v + (w - v) * ∑ i ∈ t, p i * c i := by
          rw [Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
      _ = f v + (w - v) * ∑ i ∈ t, p i * c i := by rw [hsum, one_mul]
  have e2 : ∑ i ∈ t, p i * f w = f w := by rw [← Finset.sum_mul, hsum, one_mul]
  rw [e1, e2] at h
  exact h

theorem integral_average {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] {f : ℝ → ℝ} {S : Set ℝ} {v : ℝ} (c : α → ℝ)
    (hint : Integrable c μ) (hc : ∀ᵐ a ∂μ, ∀ w ∈ S, f v + (w - v) * c a ≤ f w) :
    ∀ w ∈ S, f v + (w - v) * ∫ a, c a ∂μ ≤ f w := by
  intro w hw
  have h : ∫ a, (f v + (w - v) * c a) ∂μ ≤ ∫ _a, f w ∂μ :=
    integral_mono_ae ((integrable_const (f v)).add (hint.const_mul (w - v)))
      (integrable_const (f w)) (by filter_upwards [hc] with a ha using ha w hw)
  rw [integral_add (integrable_const _) (hint.const_mul _), integral_const_mul] at h
  simpa using h

end Subgradient

namespace Interim
namespace Problem

variable {n : ℕ}

theorem envelope_lipschitzWith (P : Problem n) : LipschitzWith 1 P.envelope := by
  refine LipschitzWith.of_dist_le_mul fun v w => ?_
  rw [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul]
  exact P.envelope_lipschitz_inequality v w

theorem subgradient_le (P : Problem n) {v w c d : ℝ} (hvw : v < w)
    (hc : ∀ u, P.envelope v + (u - v) * c ≤ P.envelope u)
    (hd : ∀ u, P.envelope w + (u - w) * d ≤ P.envelope u) : c ≤ d :=
  Subgradient.ordered hvw (hc w) (hd v)

theorem finset_average_success_subgradient (P : Problem n) (v : ℝ) {ι : Type*}
    (t : Finset ι) (p : ι → ℝ) (act : ι → Game.JointAction n)
    (hp : ∀ i ∈ t, 0 ≤ p i) (hsum : ∑ i ∈ t, p i = 1)
    (hbr : ∀ i ∈ t, P.BestResponse v (act i)) (w : ℝ) :
    P.envelope v + (w - v) * ∑ i ∈ t, p i * (P.outcome (act i)).success ≤ P.envelope w :=
  Subgradient.finset_average (S := Set.univ) t p (fun i => (P.outcome (act i)).success) hp hsum
    (fun i hi u _ => P.supporting_line v (act i) (hbr i hi) u) w (Set.mem_univ w)

theorem integral_average_success_subgradient (P : Problem n) (v : ℝ) {α : Type*}
    [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (act : α → Game.JointAction n)
    (hmeas : AEStronglyMeasurable (fun a => (P.outcome (act a)).success) μ)
    (hbr : ∀ᵐ a ∂μ, P.BestResponse v (act a)) (w : ℝ) :
    P.envelope v + (w - v) * ∫ a, (P.outcome (act a)).success ∂μ ≤ P.envelope w := by
  have hint : Integrable (fun a => (P.outcome (act a)).success) μ := by
    refine Integrable.of_bound hmeas 1 (ae_of_all _ fun a => ?_)
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [(P.outcome (act a)).success_nonneg], (P.outcome (act a)).success_le_one⟩
  refine Subgradient.integral_average (S := Set.univ) μ _ hint ?_ w (Set.mem_univ w)
  filter_upwards [hbr] with a ha u _ using P.supporting_line v (act a) ha u

theorem envelope_sub_eq_integral_of_subgradient (P : Problem n) {x y : ℝ} (hxy : x ≤ y)
    (s : ℝ → ℝ) (hs : ∀ v ∈ Icc x y, ∀ w, P.envelope v + (w - v) * s v ≤ P.envelope w) :
    P.envelope y - P.envelope x = ∫ v in x..y, s v :=
  Subgradient.sub_eq_integral hxy fun v hv w _ => hs v hv w

theorem envelope_sub_eq_integral_of_bestResponse (P : Problem n) {x y : ℝ} (hxy : x ≤ y)
    (sel : ℝ → Game.JointAction n) (hsel : ∀ v ∈ Icc x y, P.BestResponse v (sel v)) :
    P.envelope y - P.envelope x = ∫ v in x..y, (P.outcome (sel v)).success :=
  P.envelope_sub_eq_integral_of_subgradient hxy _ fun v hv w =>
    P.supporting_line v (sel v) (hsel v hv) w

theorem envelope_sub_eq_integral_of_ae_subgradient (P : Problem n) {x y : ℝ} (hxy : x ≤ y)
    (s : ℝ → ℝ)
    (hs : ∀ᵐ v, v ∈ Icc x y → ∀ w, P.envelope v + (w - v) * s v ≤ P.envelope w) :
    P.envelope y - P.envelope x = ∫ v in x..y, s v := by
  refine Subgradient.sub_eq_integral_of_ae_subgradient P.envelope_convex
    (by simp only [interior_univ]; exact Set.subset_univ _) hxy ?_
  filter_upwards [hs] with v hv hvI w _ using hv hvI w

theorem envelope_sub_eq_integral_of_ae_bestResponse (P : Problem n) {x y : ℝ} (hxy : x ≤ y)
    (sel : ℝ → Game.JointAction n)
    (hsel : ∀ᵐ v, v ∈ Icc x y → P.BestResponse v (sel v)) :
    P.envelope y - P.envelope x = ∫ v in x..y, (P.outcome (sel v)).success := by
  refine P.envelope_sub_eq_integral_of_ae_subgradient hxy _ ?_
  filter_upwards [hsel] with v hv hvI w using P.supporting_line v (sel v) (hv hvI) w

theorem finite_envelope (P : Problem n) :
    (∀ v w : ℝ, v < w → ∀ a b : Game.JointAction n, P.BestResponse v a →
      P.BestResponse w b → (P.outcome a).success ≤ (P.outcome b).success) ∧
    ConvexOn ℝ Set.univ P.envelope ∧
    (∀ v, 0 ≤ P.envelope v) ∧
    LipschitzWith 1 P.envelope ∧
    P.envelope P.g = 0 ∧
    (∀ (v : ℝ) (a : Game.JointAction n), P.BestResponse v a →
      ∀ w, P.envelope v + (w - v) * (P.outcome a).success ≤ P.envelope w) ∧
    (∀ x y : ℝ, x ≤ y → ∀ sel : ℝ → Game.JointAction n,
      (∀ᵐ v, v ∈ Icc x y → P.BestResponse v (sel v)) →
      P.envelope y - P.envelope x = ∫ v in x..y, (P.outcome (sel v)).success) ∧
    (∀ x y : ℝ, x ≤ y → ∀ s : ℝ → ℝ,
      (∀ᵐ v, v ∈ Icc x y → ∀ w, P.envelope v + (w - v) * s v ≤ P.envelope w) →
      P.envelope y - P.envelope x = ∫ v in x..y, s v) :=
  ⟨fun v w hvw a b ha hb => P.success_order v w hvw a b ha hb,
    P.envelope_convex,
    P.envelope_nonneg,
    P.envelope_lipschitzWith,
    P.envelope_at_base,
    fun v a ha w => P.supporting_line v a ha w,
    fun _ _ hxy sel hsel => P.envelope_sub_eq_integral_of_ae_bestResponse hxy sel hsel,
    fun _ _ hxy s hs => P.envelope_sub_eq_integral_of_ae_subgradient hxy s hs⟩

noncomputable def strictReserveExample : Problem 1 where
  A := Schedule.ppi 1
  G := Schedule.ppi 1
  g := 0
  g_nonneg := le_rfl
  outcome a := if a.routeCount = 1 ∧ 1 < a.bid then FiniteLaw.dirac 1 else FiniteLaw.dirac 0
  abstention := by simp [abstain]

theorem strictReserveExample_payoff (v : ℝ) (a : Game.JointAction 1) :
    strictReserveExample.payoff v a = if a.routeCount = 1 ∧ 1 < a.bid then v - a.bid else 0 := by
  unfold payoff CountLaw.utility
  simp only [strictReserveExample]
  split_ifs <;> simp [userPayoff, successIndicator, Schedule.ppi]

theorem strictReserveExample_no_bestResponse :
    ¬ ∃ a, strictReserveExample.BestResponse 2 a := by
  rintro ⟨a, ha⟩
  by_cases h : a.routeCount = 1 ∧ 1 < a.bid
  · have hb := ha ⟨(1 + a.bid) / 2, by linarith [h.2], 1, le_rfl⟩
    rw [strictReserveExample_payoff, strictReserveExample_payoff, if_pos h,
      if_pos ⟨rfl, by linarith [h.2]⟩] at hb
    linarith [h.2]
  · have hb := ha ⟨3 / 2, by norm_num, 1, le_rfl⟩
    rw [strictReserveExample_payoff, strictReserveExample_payoff, if_neg h,
      if_pos ⟨rfl, by norm_num⟩] at hb
    linarith

end Problem
end Interim

end FCAppendix
