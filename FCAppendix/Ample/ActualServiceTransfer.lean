import FCAppendix.Ample.StrictSlack
import FCAppendix.Ample.ActualAggregateTransfer
import FCAppendix.Ample.ActualNormalizationFinite

noncomputable section
namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology Real
open scoped BigOperators ENNReal
open Ample
variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem all_identity_service_from_envelope
    {M C : ℕ → ℕ} {Γ : ∀ t, FiniteGame (M t) n (C t) Seed}
    {B : ∀ t, PosteriorSystem (Γ t)} {F : Measure ℝ} {g rho : ℝ}
    (h : ReceiptSequenceAssumptions M C Γ B F g 1 rho)
    (hg : F {g} = 0) (hample : F.real (Ioi g) < (n : ℝ) * rho)
    (hppi : ∀ t, (Γ t).A = Schedule.ppi n) :
    ∀ w > 0, ∀ eps > 0, ∀ᶠ t in atTop, ∀ i : Fin (M t), ∀ a : JointAction n,
      (problem (Γ t) i).BestResponse (w + g) a →
        1 - ((problem (Γ t) i).outcome a).success < eps ∧ a.bid < eps := by
  letI : IsProbabilityMeasure F := by
    rw [← h.common_values 0]
    infer_instance
  intro w hw eps heps
  let d : ℝ := min (eps * w) (min (w / 2) (eps / 2))
  have hd : 0 < d := lt_min (mul_pos heps hw) (lt_min (half_pos hw) (half_pos heps))
  have hdw : d ≤ eps * w := min_le_left _ _
  have hhalf : d ≤ w / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hbid : d ≤ eps / 2 := (min_le_right _ _).trans (min_le_right _ _)
  filter_upwards [h.ample_envelope_uniform hg (by simpa using hample) (w + g) d hd]
    with t ht
  intro i a hbr
  have henv := ht i (w + g) le_rfl
  simp only [add_sub_cancel_right, max_eq_left hw.le] at henv
  have hbr' : (problem (Γ t) i).BestResponse (w + (problem (Γ t) i).g) a := by
    change (problem (Γ t) i).BestResponse (w + (Γ t).g) a
    simpa only [h.common_fee t] using hbr
  have hdef : Ample.deficit (problem (Γ t) i) w < d := by
    change w - (problem (Γ t) i).envelope (w + (Γ t).g) < d
    rw [h.common_fee t]
    linarith [(abs_lt.mp henv).1]
  have hc := Ample.deficit_controls (problem (Γ t) i) w hw a hbr'
  have hf : 1 - ((problem (Γ t) i).outcome a).success < eps :=
    hc.1.trans_lt ((div_lt_iff₀ hw).mpr (hdef.trans_le hdw))
  have hfhalf : 1 - ((problem (Γ t) i).outcome a).success < 1 / 2 := by
    apply hc.1.trans_lt
    apply (div_lt_iff₀ hw).mpr
    have hh := hdef.trans_le hhalf
    linarith
  have hs : (1 / 2 : ℝ) < ((problem (Γ t) i).outcome a).success := by
    linarith
  have hpay : a.bid * ((problem (Γ t) i).outcome a).load ≤
      Ample.deficit (problem (Γ t) i) w := by
    have hh := hc.2
    change a.bid * ((problem (Γ t) i).outcome a).charge (Γ t).A ≤ _ at hh
    simpa only [hppi t, CountLaw.charge_ppi] using hh
  have hlow := mul_le_mul_of_nonneg_left
    ((problem (Γ t) i).outcome a).success_le_load a.bid_nonneg
  have hbidhalf : a.bid / 2 ≤ a.bid * ((problem (Γ t) i).outcome a).success := by
    have hh := mul_le_mul_of_nonneg_left hs.le a.bid_nonneg
    linarith
  have hbidlt : a.bid / 2 < eps / 2 :=
    hbidhalf.trans_lt ((hlow.trans hpay).trans_lt (hdef.trans_le hbid))
  exact ⟨hf, by linarith⟩

namespace FreeBaseAmpleSequence
variable {M C : ℕ → ℕ} {Γ : ∀ t, FiniteGame (M t) n (C t) Seed}
  {B : ∀ t, PosteriorSystem (Γ t)} {F : Measure ℝ} {g rho : ℝ}
  (h : FreeBaseAmpleSequence M C Γ B F g rho)
include h

theorem joint_copy_error_of_positive_copy_bound
    (e : ℕ → ℝ) (he : ∀ᶠ t in atTop, 0 ≤ e t)
    (hcopy : ∀ᶠ t in atTop, ∀ i : Fin (M t), ∀ a : JointAction n, 0 < a.bid →
      ((problem (Γ t) i).outcome a).prob (fun r => r.val ≠ a.routeCount) ≤ e t) :
    ∀ᶠ t in atTop, ∀ i : Fin (M t), ∀ᵐ x ∂((Γ t).F ⊗ₘ (Γ t).σ),
      ((problem (Γ t) i).outcome x.2).prob (fun r => r.val ≠ x.2.routeCount) ≤ e t := by
  filter_upwards [h.eventually_finite_guards, he, hcopy] with t ht het hct
  have hrouted := ppi_ae_routed_bid_pos (Γ t) (by omega) h.proposers_pos ht.2.1
    (h.ppi t) (h.visible_atomless t) (h.feasible_continuations t)
    (h.users t) (h.abstention t) (h.reject_zero t)
  intro i
  filter_upwards [hrouted] with x hx
  by_cases hk : x.2.routeCount = 0
  · rw [outcome_copy_error_zero_of_route_zero (Γ t) i x.2 hk]
    exact het
  · exact hct i x.2 (hx (Nat.pos_of_ne_zero hk))

theorem chosen_realized_copy_error {kappa : ℝ}
    (hcopy : ∀ᶠ t in atTop, ∀ i : Fin (M t),
      (∀ a : JointAction n, 0 < a.bid →
        ((problem (Γ t) i).outcome a).prob (fun r => r.val ≠ a.routeCount) ≤
          n * exp (-kappa * M t)) ∧
      (∀ w : ℝ, 0 < w → ∀ a : JointAction n,
        (problem (Γ t) i).BestResponse (w + (Γ t).g) a →
          a.bid ≤ 2 * w * exp (-kappa * M t))) :
    ∀ j : ℕ,
      (∀ᶠ t in atTop, |actualInclusionMass (Γ t) j - actualRouteMass (Γ t) j| ≤
        n * exp (-kappa * M t)) ∧
      (∀ᶠ t in atTop, |actualPopulationInclusionMass (Γ t) j - actualRouteMass (Γ t) j| ≤
        n * exp (-kappa * M t)) := by
  have hnonneg : ∀ t, (0 : ℝ) ≤ n * exp (-kappa * M t) :=
    fun t => mul_nonneg (Nat.cast_nonneg n) (exp_pos _).le
  have hjoint := h.joint_copy_error_of_positive_copy_bound
    (fun t => (n : ℝ) * exp (-kappa * M t)) (Filter.Eventually.of_forall hnonneg)
    (hcopy.mono fun t ht i => (ht i).1)
  have herr : ∀ᶠ t in atTop, ∀ j : ℕ,
      |actualInclusionMass (Γ t) j - actualRouteMass (Γ t) j| ≤ n * exp (-kappa * M t) ∧
      |actualPopulationInclusionMass (Γ t) j - actualRouteMass (Γ t) j| ≤
        n * exp (-kappa * M t) := by
    filter_upwards [h.eventually_finite_guards, hjoint] with t ht hc
    exact actual_count_error_of_copy_error (Γ t) (by omega) _ (hnonneg t) hc
  intro j
  exact ⟨herr.mono fun t ht => (ht j).1, herr.mono fun t ht => (ht j).2⟩

theorem zero_route_limit :
    Tendsto (fun t => actualRouteMass (Γ t) 0) atTop (𝓝 (1 - F.real (Ioi g))) := by
  letI := h.probability
  apply tendsto_const_nhds.congr'
  filter_upwards [h.eventually_finite_guards] with t ht
  have hdraw := ppi_ae_positive_draw_iff (Γ t) (by omega) h.proposers_pos ht.2.1
    (h.ppi t) (h.visible_atomless t) (h.feasible_continuations t)
    (h.users t) (h.abstention t) (h.reject_zero t)
  have heq : actualRouteMass (Γ t) 0 = (Γ t).F.real (Iic (Γ t).g) := by
    rw [← joint_value_probability (Γ t) (Iic (Γ t).g) measurableSet_Iic]
    apply measureReal_congr
    filter_upwards [hdraw, h.abstention t] with x hx hxa
    apply propext
    change x.2.routeCount = 0 ↔ x.1 ≤ (Γ t).g
    constructor
    · intro hk
      by_contra hv
      have hp := (hx.mpr (lt_of_not_ge hv)).2
      omega
    · intro hv
      exact hxa hv
  rw [heq, h.common_values t, h.common_fee t]
  have hc : (Ioi g)ᶜ = Iic g := by ext x; simp
  rw [← hc, measureReal_compl measurableSet_Ioi, probReal_univ]

theorem all_identity_service_from_envelope :
    ∀ w > 0, ∀ eps > 0, ∀ᶠ t in atTop, ∀ i : Fin (M t), ∀ a : JointAction n,
      (problem (Γ t) i).BestResponse (w + g) a →
        1 - ((problem (Γ t) i).outcome a).success < eps ∧ a.bid < eps :=
  FCAppendix.Bayes.all_identity_service_from_envelope h.receipt (h.atomless_values g) h.ample h.ppi

end FreeBaseAmpleSequence
end FCAppendix.Bayes
