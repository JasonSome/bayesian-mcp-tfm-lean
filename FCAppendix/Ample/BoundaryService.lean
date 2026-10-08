import FCAppendix.Ample.BoundaryPrimitives
import FCAppendix.Ample.SlackSingleton
import FCAppendix.Ample.SlackFiniteService
import FCAppendix.Ample.RouteCoupling
import FCAppendix.Ample.CommonRateActualAdapters
import FCAppendix.Ample.ActualAggregateTransfer

noncomputable section
namespace FCAppendix.Bayes.CompletionDraft
open MeasureTheory ProbabilityTheory Game Set Filter Topology Real
open scoped BigOperators

variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]
  {M C : ℕ → ℕ} {Γ : ∀ t, FiniteGame (M t) n (C t) Seed}
  {B : ∀ t, PosteriorSystem (Γ t)} {F : Measure ℝ} {g : ℝ}

structure BoundaryAcceptanceConclusion
    (M C : ℕ → ℕ) (Γ : ∀ t, FiniteGame (M t) n (C t) Seed)
    (F : Measure ℝ) (g : ℝ) : Prop where
  participation : Tendsto (fun t => ∑ j ∈ Finset.Icc 1 n,
    actualRouteMass (Γ t) j) atTop (𝓝 (F.real (Ioi g)))
  singleton_floor : ∃ a > 0, ∀ᶠ t in atTop, a ≤ actualRouteMass (Γ t) 1
  mean_gap : ∃ delta > 0, ∀ᶠ t in atTop,
    (∑ j ∈ Finset.Icc 1 n, (j : ℝ) * actualRouteMass (Γ t) j) / n ≤ 1-delta
  count_error : ∃ kappa > 0, ∀ᶠ t in atTop, ∀ j,
    |actualInclusionMass (Γ t) j - actualRouteMass (Γ t) j| ≤
      n * exp (-kappa * M t)
  population_count_error : ∃ kappa > 0, ∀ᶠ t in atTop, ∀ j,
    |actualPopulationInclusionMass (Γ t) j - actualRouteMass (Γ t) j| ≤
      n * exp (-kappa * M t)
  acceptance : ∀ eps > 0, ∀ᶠ t in atTop, ∀ᵐ x ∂activeDrawLaw (Γ t),
    0 < x.2.routeCount →
      |actualMeanLoad (Γ t) x.2 / (x.2.routeCount : ℝ) - 1| ≤ eps

namespace FreeBaseBoundarySequence
variable (h : FreeBaseBoundarySequence M C Γ B F g)
include h

theorem eventually_exact_participation :
    ∀ᶠ t in atTop,
      positiveRouteMass (Γ t) (fun _ => True) = F.real (Ioi g) ∧
      submittedMarginal (Γ t) = Ample.contactMarginal n (visibleClassMass (Γ t) 0) := by
  filter_upwards [h.eventually_finite_guards] with t ht
  have hn : 0 < n := by have := h.proposers_two; omega
  refine ⟨?_, ppi_submitted_eq_positive (Γ t) (by omega) hn ht.2.1
    (h.ppi t) (h.visible_atomless t) (h.feasible_continuations t)
    (h.users t) (h.abstention t) (h.reject_zero t)⟩
  simpa only [h.common_values t, h.common_fee t] using
    ppi_positiveParticipation_eq (Γ t) (by omega) hn ht.2.1
      (h.ppi t) (h.visible_atomless t) (h.feasible_continuations t)
      (h.users t) (h.abstention t) (h.reject_zero t)

theorem eventually_route_class_eq :
    ∀ᶠ t in atTop, ∀ j : ℕ, 1 ≤ j →
      actualRouteMass (Γ t) j = visibleClassMass (Γ t) 0 j := by
  filter_upwards [h.eventually_finite_guards] with t ht
  intro j hj
  have hn : 0 < n := by have := h.proposers_two; omega
  have hraw := ppi_positiveRouteMass_eq_raw (Γ t) (by omega) hn ht.2.1
    (h.ppi t) (h.visible_atomless t) (h.feasible_continuations t)
    (h.users t) (h.abstention t) (h.reject_zero t) (fun k => k = j)
    (fun k hk => by omega)
  exact hraw.symm.trans (positiveRouteMass_class_eq (Γ t) hj)

theorem participation :
    Tendsto (fun t => ∑ j ∈ Finset.Icc 1 n, actualRouteMass (Γ t) j)
      atTop (𝓝 (F.real (Ioi g))) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [h.eventually_exact_participation, h.eventually_route_class_eq]
    with t hp hc
  calc
    F.real (Ioi g) = positiveRouteMass (Γ t) (fun _ => True) := hp.1.symm
    _ = ∑ j ∈ Finset.Icc 1 n, visibleClassMass (Γ t) 0 j :=
      positiveRouteMass_sum_classes (Γ t)
    _ = ∑ j ∈ Finset.Icc 1 n, actualRouteMass (Γ t) j := by
      apply Finset.sum_congr rfl
      intro j hj
      exact (hc j (Finset.mem_Icc.mp hj).1).symm

theorem singleton_floor :
    ∃ a > 0, ∀ᶠ t in atTop, a ≤ actualRouteMass (Γ t) 1 := by
  have hn : 0 < n := by have := h.proposers_two; omega
  obtain ⟨a, ha, hf⟩ := ppi_singleton_floor_of_source_sequence Γ F g 1 hn
    (by norm_num) h.common_values h.common_fee h.active_pos
    h.population_grows h.capacity_ratio h.eventually_finite_guards h.users
    h.feasible_continuations h.visible_atomless h.ppi h.free h.abstention h.reject_zero
  refine ⟨a, ha, ?_⟩
  filter_upwards [hf, h.eventually_route_class_eq] with t ht hc
  rw [hc 1 le_rfl, ← positiveRouteMass_class_eq (Γ t) le_rfl]
  exact ht

theorem eventually_submitted_eq_route_mean :
    ∀ᶠ t in atTop, submittedMarginal (Γ t) =
      (∑ j ∈ Finset.Icc 1 n, (j : ℝ) * actualRouteMass (Γ t) j) / n := by
  filter_upwards [h.eventually_exact_participation, h.eventually_route_class_eq]
    with t hp hc
  rw [hp.2, Ample.contactMarginal]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [hc j (Finset.mem_Icc.mp hj).1]
  ring

theorem mean_gap :
    ∃ delta > 0, ∀ᶠ t in atTop,
      (∑ j ∈ Finset.Icc 1 n, (j : ℝ) * actualRouteMass (Γ t) j) / n ≤ 1-delta := by
  obtain ⟨a, ha, hf⟩ := h.singleton_floor
  exact Ample.CompletionDraft.eventually_mean_gap_of_singleton_floor h.proposers_two
    (fun t j => actualRouteMass (Γ t) j)
    (fun _ _ _ => measureReal_nonneg) h.active_le_one ha h.participation hf

theorem strict_submitted_margin :
    ∃ eta > 0, ∀ᶠ t in atTop, submittedMarginal (Γ t) ≤ 1-eta := by
  obtain ⟨eta, heta, hgap⟩ := h.mean_gap
  refine ⟨eta, heta, ?_⟩
  filter_upwards [hgap, h.eventually_submitted_eq_route_mean] with t hg he
  rwa [he]

theorem uniform_exponential :
    ∃ kappa : ℝ, 0 < kappa ∧ ∀ᶠ t in atTop, ∀ i : Fin (M t),
      (∀ b : ℝ, 0 < b →
        1 - meanAcceptProb (Γ t) i b ≤ exp (-kappa * M t)) ∧
      (∀ w : ℝ, 0 ≤ w → Ample.deficit (problem (Γ t) i) w ≤
        w * exp (-kappa * M t)) ∧
      (∀ a : JointAction n, 0 < a.bid →
        ((problem (Γ t) i).outcome a).prob (fun r => r.val ≠ a.routeCount) ≤
          n * exp (-kappa * M t)) ∧
      (∀ w : ℝ, 0 < w → ∀ a : JointAction n,
        (problem (Γ t) i).BestResponse (w + (Γ t).g) a →
          1 - ((problem (Γ t) i).outcome a).success ≤ exp (-kappa * M t) ∧
          a.bid ≤ 2 * w * exp (-kappa * M t)) := by
  obtain ⟨eta, heta, hmarg⟩ := h.strict_submitted_margin
  exact ppi_source_exponential_of_margin Γ
    (by have := h.proposers_two; omega) h.population_grows h.capacity_ratio
    heta hmarg h.ppi h.free h.visible_atomless h.feasible_continuations

theorem all_count_errors :
    ∃ kappa > 0, ∀ᶠ t in atTop, ∀ j : ℕ,
      |actualInclusionMass (Γ t) j - actualRouteMass (Γ t) j| ≤
          n * exp (-kappa * M t) ∧
      |actualPopulationInclusionMass (Γ t) j - actualRouteMass (Γ t) j| ≤
          n * exp (-kappa * M t) := by
  obtain ⟨kappa, hkappa, hexp⟩ := h.uniform_exponential
  refine ⟨kappa, hkappa, ?_⟩
  filter_upwards [h.eventually_finite_guards, hexp] with t ht hq
  have hn : 0 < n := by have := h.proposers_two; omega
  have hb := ppi_ae_routed_bid_pos (Γ t) (by omega) hn ht.2.1
    (h.ppi t) (h.visible_atomless t) (h.feasible_continuations t)
    (h.users t) (h.abstention t) (h.reject_zero t)
  apply actual_count_error_of_copy_error (Γ t) (by omega)
    (n * exp (-kappa * M t)) (mul_nonneg (Nat.cast_nonneg n) (exp_pos _).le)
  intro i
  filter_upwards [hb] with x hx
  exact chosen_realized_mismatch_le_error (Γ t) hn i x.2 (exp_pos _).le
    (fun hk => (hq i).1 x.2.bid (hx hk))

theorem active_uniform_acceptance :
    ∀ eps > 0, ∀ᶠ t in atTop, ∀ᵐ x ∂activeDrawLaw (Γ t),
      0 < x.2.routeCount →
        |actualMeanLoad (Γ t) x.2 / (x.2.routeCount : ℝ) - 1| ≤ eps := by
  obtain ⟨kappa, hkappa, hexp⟩ := h.uniform_exponential
  intro eps heps
  filter_upwards [h.eventually_finite_guards, hexp,
    (Ample.exp_neg_population_tendsto_zero h.population_grows hkappa).eventually_lt_const heps]
    with t ht hq herr
  have hm : 0 < M t := by omega
  have hn : 0 < n := by have := h.proposers_two; omega
  let i : Fin (M t) := ⟨0, hm⟩
  have hb := ppi_ae_routed_bid_pos (Γ t) hm hn ht.2.1
    (h.ppi t) (h.visible_atomless t) (h.feasible_continuations t)
    (h.users t) (h.abstention t) (h.reject_zero t)
  have hae : ∀ᵐ x ∂((Γ t).F ⊗ₘ (Γ t).σ), 0 < x.2.routeCount →
      |actualMeanLoad (Γ t) x.2 / (x.2.routeCount : ℝ) - 1| ≤ eps := by
    filter_upwards [hb] with x hx hk
    have hkR : (0 : ℝ) < x.2.routeCount := Nat.cast_pos.mpr hk
    have hmean : actualMeanLoad (Γ t) x.2 / (x.2.routeCount : ℝ) =
        meanAcceptProb (Γ t) i x.2.bid := by
      rw [actualMeanLoad, dif_pos hm, load_eq_mean (Γ t) hn]
      exact mul_div_cancel_left₀ _ hkR.ne'
    have hle : meanAcceptProb (Γ t) i x.2.bid ≤ 1 := by
      have hh := ((problem (Γ t) i).outcome (sameBidSingleton hn x.2)).success_le_one
      rwa [singleton_success (Γ t) hn i _ rfl] at hh
    rw [hmean, abs_of_nonpos (sub_nonpos.mpr hle)]
    have hh := ((hq i).1 x.2.bid (hx hk)).trans herr.le
    linarith
  change ∀ᵐ x ∂(((Γ t).F (Ioi (Γ t).g))⁻¹ •
    ((Γ t).F ⊗ₘ (Γ t).σ).restrict {x | (Γ t).g < x.1}), _
  exact Measure.ae_smul_measure (ae_restrict_of_ae hae) _

theorem acceptance : BoundaryAcceptanceConclusion M C Γ F g := by
  obtain ⟨kappa, hkappa, he⟩ := h.all_count_errors
  refine ⟨h.participation, h.singleton_floor, h.mean_gap,
    ⟨kappa, hkappa, ?_⟩, ⟨kappa, hkappa, ?_⟩, h.active_uniform_acceptance⟩
  · filter_upwards [he] with t ht
    exact fun j => (ht j).1
  · filter_upwards [he] with t ht
    exact fun j => (ht j).2

theorem coverage_error :
    ∃ kappa > 0, ∀ᶠ t in atTop,
      0 ≤ F.real (Ioi g) - finiteCoverage (Γ t) ∧
      F.real (Ioi g) - finiteCoverage (Γ t) ≤ exp (-kappa * M t) := by
  obtain ⟨kappa, hkappa, hexp⟩ := h.uniform_exponential
  refine ⟨kappa, hkappa, ?_⟩
  filter_upwards [h.eventually_finite_guards, h.eventually_exact_participation, hexp]
    with t ht hp hq
  have hm : 0 < M t := by omega
  have hn : 0 < n := by have := h.proposers_two; omega
  have hlo := coverage_ge_positiveParticipation_sub_error (Γ t) hm hn
    (exp_pos (-kappa * M t)).le (fun i => (hq i).1)
  have hhi := finiteCoverage_le_positiveParticipation (Γ t) hm hn (h.reject_zero t)
  rw [hp.1] at hlo hhi
  constructor <;> linarith

theorem coverage_tendsto :
    Tendsto (fun t => finiteCoverage (Γ t)) atTop (𝓝 (F.real (Ioi g))) := by
  obtain ⟨kappa, hkappa, he⟩ := h.coverage_error
  have hlim : Tendsto (fun t => F.real (Ioi g) - exp (-kappa * M t))
      atTop (𝓝 (F.real (Ioi g))) := by
    simpa only [sub_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => F.real (Ioi g))
        atTop (𝓝 (F.real (Ioi g)))).sub
        (Ample.exp_neg_population_tendsto_zero h.population_grows hkappa)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlim tendsto_const_nhds
  · filter_upwards [he] with t ht
    linarith [ht.2]
  · filter_upwards [he] with t ht
    linarith [ht.1]

theorem compact_supported_service {lo hi : ℝ} (hlo : 0 < lo) (hlohi : lo ≤ hi) :
    ∀ eps > 0, ∀ᶠ t in atTop, ∀ i : Fin (M t), ∀ w ∈ Icc lo hi,
      ∀ a : JointAction n, (problem (Γ t) i).BestResponse (w+g) a →
        1 - ((problem (Γ t) i).outcome a).success < eps ∧ a.bid < eps := by
  obtain ⟨kappa, hkappa, hexp⟩ := h.uniform_exponential
  have hhi : 0 < hi := hlo.trans_le hlohi
  intro eps heps
  have hb := (Ample.exp_neg_population_tendsto_zero h.population_grows hkappa).const_mul (2*hi)
  simp only [mul_zero] at hb
  filter_upwards [hexp,
    (Ample.exp_neg_population_tendsto_zero h.population_grows hkappa).eventually_lt_const heps,
    hb.eventually_lt_const heps] with t ht hs hbid
  intro i w hw a ha
  have hh := (ht i).2.2.2 w (hlo.trans_le hw.1) a
    (by simpa only [h.common_fee t] using ha)
  refine ⟨hh.1.trans_lt hs, hh.2.trans_lt ?_⟩
  calc
    2*w*exp (-kappa*M t) ≤ 2*hi*exp (-kappa*M t) :=
      mul_le_mul (by linarith [hw.2]) le_rfl (exp_pos _).le
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hhi.le)
    _ < eps := hbid

theorem envelope_uniform (H : ℝ) :
    ∀ eps > 0, ∀ᶠ t in atTop, ∀ i : Fin (M t), ∀ w : ℝ,
      0 ≤ w → w ≤ H → |(problem (Γ t) i).envelope (w+g) - w| < eps := by
  obtain ⟨kappa, hkappa, hexp⟩ := h.uniform_exponential
  have herr := (Ample.exp_neg_population_tendsto_zero h.population_grows hkappa).const_mul
    (max H 0)
  simp only [mul_zero] at herr
  intro eps heps
  filter_upwards [hexp, herr.eventually_lt_const heps] with t ht herrt
  intro i w hw hwH
  have hnonneg := Ample.deficit_nonneg (problem (Γ t) i) w hw
  have hbound := (ht i).2.1 w hw
  change 0 ≤ w - (problem (Γ t) i).envelope (w + (Γ t).g) at hnonneg
  change w - (problem (Γ t) i).envelope (w + (Γ t).g) ≤ _ at hbound
  rw [h.common_fee t] at hnonneg hbound
  have hscale : w * exp (-kappa * M t) ≤ max H 0 * exp (-kappa * M t) :=
    mul_le_mul_of_nonneg_right (hwH.trans (le_max_left H 0)) (exp_pos _).le
  rw [abs_of_nonpos (by linarith : (problem (Γ t) i).envelope (w+g) - w ≤ 0)]
  linarith

theorem all_supported_service :
    ∀ w > 0, ∀ eps > 0, ∀ᶠ t in atTop, ∀ i : Fin (M t), ∀ a : JointAction n,
      (problem (Γ t) i).BestResponse (w+g) a →
        1 - ((problem (Γ t) i).outcome a).success < eps ∧ a.bid < eps := by
  intro w hw eps heps
  filter_upwards [h.compact_supported_service hw le_rfl eps heps] with t ht
  intro i a ha
  exact ht i w ⟨le_rfl, le_rfl⟩ a ha

end FreeBaseBoundarySequence
end FCAppendix.Bayes.CompletionDraft
