import FCAppendix.Ample.SlackAssumptions
import FCAppendix.Ample.SlackParticipation
import FCAppendix.Ample.SlackEstimates

noncomputable section
namespace FCAppendix.Ample
open Filter Topology Real Set

theorem positive_floor_of_no_vanishing_subsequence (x : ℕ → ℝ)
    (hx : ∀ t, 0 ≤ x t)
    (hno : ∀ φ : ℕ → ℕ, Tendsto φ atTop atTop →
      Tendsto (fun t => x (φ t)) atTop (𝓝 0) → False) :
    ∃ a : ℝ, 0 < a ∧ ∀ᶠ t in atTop, a ≤ x t := by
  by_contra hn
  have hchoose (k : ℕ) : ∃ t, k ≤ t ∧ x t < 1 / ((k : ℝ) + 1) := by
    by_contra hh
    have he : ∀ᶠ t in atTop, 1 / ((k : ℝ) + 1) ≤ x t := by
      apply eventually_atTop.mpr
      refine ⟨k, fun t ht => ?_⟩
      exact le_of_not_gt (fun hlt => hh ⟨t, ht, hlt⟩)
    exact hn ⟨1 / ((k : ℝ) + 1), by positivity, he⟩
  choose φ hφ using hchoose
  have hc : Tendsto φ atTop atTop := by
    apply tendsto_atTop.mpr
    intro k
    filter_upwards [eventually_ge_atTop k] with t ht
    exact ht.trans (hφ t).1
  have hz : Tendsto (fun t => x (φ t)) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      tendsto_one_div_add_atTop_nhds_zero_nat
    · exact fun t => hx (φ t)
    · exact fun t => (hφ t).2.le
  exact hno φ hc hz

lemma exp_neg_population_tendsto_zero {M : ℕ → ℕ}
    (hM : Tendsto M atTop atTop) {J : ℝ} (hJ : 0 < J) :
    Tendsto (fun t => exp (-J * M t)) atTop (𝓝 0) := by
  have ht := tendsto_exp_neg_atTop_nhds_zero.comp
    ((tendsto_natCast_atTop_atTop.comp hM).const_mul_atTop hJ)
  convert ht using 1
  ext t
  dsimp only [Function.comp_apply]
  congr 1
  ring

theorem eventually_two_error_gain {M : ℕ → ℕ} (hM : Tendsto M atTop atTop)
    {ε H₀ H₁ L J : ℝ} (hε : 0 < ε) (_hH₀ : 0 ≤ H₀) (hH₁ : 0 ≤ H₁)
    (hJ : 0 < J) (hLJ : L < J) :
    ∀ᶠ t in atTop,
      exp (-J * M t) < 1 / 2 ∧
      H₀ * exp (-J * M t) + H₁ * exp (-J * M t) / (1 - exp (-J * M t)) <
        ε * exp (-L * M t) := by
  have hr := exp_neg_population_tendsto_zero hM hJ
  have hratio := (exp_neg_population_tendsto_zero hM (sub_pos.mpr hLJ)).const_mul
    (H₀ + 2 * H₁)
  simp only [mul_zero] at hratio
  filter_upwards [hr.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2),
    hratio.eventually_lt_const hε] with t ht hg
  refine ⟨ht, ?_⟩
  have hden : 0 < 1 - exp (-J * M t) := by linarith
  have hquot : H₁ * exp (-J * M t) / (1 - exp (-J * M t)) ≤
      2 * H₁ * exp (-J * M t) := by
    apply (div_le_iff₀ hden).mpr
    have hmul := mul_nonneg (mul_nonneg hH₁ (exp_pos (-J * M t)).le)
      (show 0 ≤ 1 - 2 * exp (-J * M t) by linarith)
    nlinarith
  have hfactor : exp (-J * M t) =
      exp (-(J - L) * M t) * exp (-L * M t) := by
    rw [← exp_add]
    congr 1
    ring
  have hmul := mul_lt_mul_of_pos_right hg (exp_pos (-L * M t))
  calc
    _ ≤ (H₀ + 2 * H₁) * exp (-J * M t) := by linarith
    _ < _ := by rw [hfactor]; nlinarith

lemma exp_log_le_rival_power {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    {m : ℕ} (hm : 0 < m) : exp (-(-log s) * m) ≤ s ^ (m - 1) := by
  have he : exp (-(-log s) * m) = s ^ m := by
    rw [neg_neg, mul_comm, exp_nat_mul, exp_log hs]
  rw [he]
  have heM : m = (m - 1) + 1 := by omega
  conv_lhs => rw [heM, pow_succ]
  exact mul_le_of_le_one_right (pow_nonneg hs.le _) hs1

lemma rival_hoeffding_le_full {m : ℕ} (hm : 2 ≤ m) (δ : ℝ) :
    exp (-2 * (m - 1 : ℕ) * δ ^ 2) ≤ exp (-(δ ^ 2) * m) := by
  apply exp_le_exp.mpr
  have hn : 1 ≤ m := by omega
  rw [Nat.cast_sub hn, Nat.cast_one]
  have hmr : (2 : ℝ) ≤ m := by exact_mod_cast hm
  nlinarith [sq_nonneg δ]

end FCAppendix.Ample

namespace FCAppendix.Bayes.FreeBaseAmpleSequence
open MeasureTheory ProbabilityTheory Game Set Filter Topology Real
variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]
  {M C : ℕ → ℕ} {Γ : ∀ t, FiniteGame (M t) n (C t) Seed}
  {B : ∀ t, PosteriorSystem (Γ t)} {F : Measure ℝ} {g ρ : ℝ}
  (h : FreeBaseAmpleSequence M C Γ B F g ρ)

include h

lemma eventually_exact_participation :
    ∀ᶠ t in atTop,
      positiveRouteMass (Γ t) (fun _ => True) = F.real (Ioi g) ∧
      submittedMarginal (Γ t) = Ample.contactMarginal n (visibleClassMass (Γ t) 0) := by
  filter_upwards [h.eventually_finite_guards] with t ht
  refine ⟨?_, ppi_submitted_eq_positive (Γ t) (by omega) h.proposers_pos ht.2.1
    (h.ppi t) (h.visible_atomless t) (h.feasible_continuations t) (h.users t)
    (h.abstention t) (h.reject_zero t)⟩
  simpa only [h.common_values t, h.common_fee t] using
    ppi_positiveParticipation_eq (Γ t) (by omega) h.proposers_pos ht.2.1
      (h.ppi t) (h.visible_atomless t) (h.feasible_continuations t) (h.users t)
      (h.abstention t) (h.reject_zero t)

lemma compact_service {ε H : ℝ} (hε : 0 < ε) :
    ∀ᶠ t in atTop, ∀ (i : Fin (M t)) (w : ℝ), w ∈ Icc ε H →
      ∀ a : JointAction n, (problem (Γ t) i).BestResponse (w + (Γ t).g) a →
        1 / 2 < ((problem (Γ t) i).outcome a).success := by
  letI := h.probability
  filter_upwards [h.receipt.ample_envelope_uniform (h.atomless_values g)
    (by simpa using h.ample) (H + g) (ε / 4) (by positivity)] with t ht
  intro i w hw a ha
  have hw0 : 0 < w := hε.trans_le hw.1
  have hd := ht i (w + (Γ t).g) (by rw [h.common_fee t]; linarith [hw.2])
  rw [h.common_fee t, add_sub_cancel_right, max_eq_left hw0.le] at hd
  have hf : Ample.deficit (problem (Γ t) i) w < ε / 4 := by
    have hh := (abs_lt.mp hd).1
    change w - (problem (Γ t) i).envelope (w + (Γ t).g) < _
    rw [h.common_fee t]
    linarith
  have hc := (Ample.deficit_controls (problem (Γ t) i) w hw0 a ha).1
  have hmul := (le_div_iff₀ hw0).mp hc
  have hs := ((problem (Γ t) i).outcome a).success_le_one
  have hprod := mul_nonneg (sub_nonneg.mpr hw.1) (sub_nonneg.mpr hs)
  nlinarith

lemma capacity_per_rival :
    Tendsto (fun t => (C t : ℝ) / (M t - 1 : ℕ)) atTop (𝓝 ρ) :=
  SimultaneousCongestion.capacity_per_rival h.population_grows h.capacity_ratio

lemma eventually_capacity_above {d : ℝ} (hd : 0 < d) :
    ∀ᶠ t in atTop, ((M t - 1 : ℕ) : ℝ) * (ρ - d) ≤ C t := by
  filter_upwards [h.eventually_finite_guards,
    h.capacity_per_rival.eventually_const_lt (show ρ - d < ρ by linarith)] with t ht hc
  have hN : (0 : ℝ) < (M t - 1 : ℕ) := by exact_mod_cast (show 0 < M t - 1 by omega)
  have hh := (lt_div_iff₀ hN).mp hc
  nlinarith

lemma eventually_capacity_below {d : ℝ} (hd : 0 < d) :
    ∀ᶠ t in atTop, (C t : ℝ) ≤ ((M t - 1 : ℕ) : ℝ) * (ρ + d) := by
  filter_upwards [h.eventually_finite_guards,
    h.capacity_per_rival.eventually_lt_const (show ρ < ρ + d by linarith)] with t ht hc
  have hN : (0 : ℝ) < (M t - 1 : ℕ) := by exact_mod_cast (show 0 < M t - 1 by omega)
  have hh := (div_lt_iff₀ hN).mp hc
  nlinarith

lemma compact_band {d : ℝ} (hd : 0 < d) :
    ∃ ε H : ℝ, 0 < ε ∧ ε < H ∧
      ∀ t, (Γ t).F.real {v | (Γ t).g < v ∧ v - (Γ t).g ∉ Icc ε H} < d := by
  letI := h.probability
  obtain ⟨ε, H, hε, hH, ht⟩ := Ample.exists_compact_positive_band F g hd
  exact ⟨ε, H, hε, hH, fun t => by simpa only [h.common_values t, h.common_fee t] using ht⟩

end FCAppendix.Bayes.FreeBaseAmpleSequence
