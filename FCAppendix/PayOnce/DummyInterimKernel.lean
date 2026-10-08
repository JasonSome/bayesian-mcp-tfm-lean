import FCAppendix.PayOnce.DummyProfileKernel
import FCAppendix.PayOnce.DummyFocalLimit
import FCAppendix.PayOnce.EffectiveBidLaw
import FCAppendix.PayOnce.InterimCountTransport

namespace FCAppendix.PayOnce.DummyKernel
open MeasureTheory Set CommonList
open scoped BigOperators
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem allocation_comp_equiv (e : κ ≃ ι) {n c : ℕ} (hn : 2 ≤ n)
    (r : ι → ℝ) (b : ℝ) :
    allocation n c hn (fun j => r (e j)) b = allocation n c hn r b := by
  by_cases hb : 0 < b
  · have hcard : Fintype.card (Active (fun j => r (e j))) = Fintype.card (Active r) :=
      Fintype.card_congr (e.subtypeEquiv (fun _ => Iff.rfl))
    obtain ⟨L,hL,he,hcap⟩ := allocation_root (c := c) hn r hb
    rw [he]
    apply allocation_eq_kernel hn _ hb hL
    rw [e.sum_comp (fun j => kernel n (r j) L),hcard]
    exact hcap
  · rw [allocation_eq_zero_of_nonpos hn _ (le_of_not_gt hb),
      allocation_eq_zero_of_nonpos hn _ (le_of_not_gt hb)]

theorem integral_allocation_test_equiv (e : κ ≃ ι) {n c : ℕ} (hn : 2 ≤ n)
    (G : Measure ℝ) [IsProbabilityMeasure G] (b : ℝ) (test : ℝ → ℝ) :
    (∫ r : κ → ℝ, test (allocation n c hn r b) ∂Measure.pi (fun _ : κ => G)) =
      ∫ r : ι → ℝ, test (allocation n c hn r b) ∂Measure.pi (fun _ : ι => G) := by
  have hm := measurePreserving_piCongrLeft (fun _ : κ => G) e.symm
  have hh := hm.integral_comp' (fun r : κ → ℝ => test (allocation n c hn r b))
  rw [← hh]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun r => by
    apply congrArg test
    have heval : (MeasurableEquiv.piCongrLeft (fun _ : κ => ℝ) e.symm) r =
        fun j => r (e j) := by
      funext j
      simp [MeasurableEquiv.coe_piCongrLeft,Equiv.piCongrLeft_apply]
    rw [heval]
    exact allocation_comp_equiv e hn r b

theorem allocation_monotone {n c : ℕ} (hn : 2 ≤ n) (r : ι → ℝ) :
    Monotone (allocation n c hn r) :=
  AnalyticalKernel.allocation_monotone hn (min_le_right _ _) _

theorem measurable_allocation_fixed_bid {n c : ℕ} (hn : 2 ≤ n) (b : ℝ) :
    Measurable (fun r : ι → ℝ => allocation n c hn r b) :=
  (measurable_allocation_joint hn).comp (measurable_const.prodMk measurable_id)

theorem integrable_success_allocation {n c : ℕ} (hn : 2 ≤ n)
    (μ : Measure (ι → ℝ)) [IsProbabilityMeasure μ] (b : ℝ) :
    Integrable (fun r => success n (allocation n c hn r b)) μ := by
  apply UnitInterval.integrable μ _
  · exact (show Continuous (success n) from by unfold success; fun_prop).measurable.comp
      (measurable_allocation_fixed_bid hn b)
  · intro r
    unfold success
    exact sub_nonneg.mpr (pow_le_one₀ (by linarith [(allocation_bounds (c := c) hn r b).2])
      (by linarith [(allocation_bounds (c := c) hn r b).1]))
  · intro r
    exact success_le_one n _ (allocation_bounds hn r b).2

theorem coverage_monotone {n c : ℕ} (hn : 2 ≤ n)
    (μ : Measure (ι → ℝ)) [IsProbabilityMeasure μ] : Monotone (coverage n c hn μ) := by
  intro b a hba
  apply integral_mono (integrable_success_allocation hn μ b) (integrable_success_allocation hn μ a)
  intro r
  unfold success
  have hp := allocation_monotone (c := c) hn r hba
  have ha := (allocation_bounds (c := c) hn r a).2
  have hh := pow_le_pow_left₀ (sub_nonneg.mpr ha) (by linarith :
    1-allocation n c hn r a ≤ 1-allocation n c hn r b) n
  linarith

theorem measurable_coverage {n c : ℕ} (hn : 2 ≤ n)
    (μ : Measure (ι → ℝ)) [IsProbabilityMeasure μ] : Measurable (coverage n c hn μ) :=
  (coverage_monotone hn μ).measurable

end FCAppendix.PayOnce.DummyKernel

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set
open PayOnce.CompactifiedBidLaws PayOnce.DummyKernel
variable {m n c k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

noncomputable def effectiveRivalBids (i : Fin m) (d : UserProfile m n) : Rival i → ℝ :=
  fun j => effectiveBid (d j.val).1.2

theorem measurable_effectiveRivalBids (i : Fin m) : Measurable (effectiveRivalBids (n := n) i) := by
  apply measurable_pi_lambda
  intro j
  exact (measurable_effectiveBid n).comp
    (measurable_snd.comp (measurable_fst.comp (measurable_pi_apply j.val)))

theorem effectiveRivalBids_measurePreserving (Γ : FiniteGame m n c Seed) (i : Fin m) :
    MeasurePreserving (effectiveRivalBids i) (userProfileLaw Γ)
      (Measure.pi fun _ : Rival i => (PayOnce.BidScaling.realBidLaw Γ : Measure ℝ)) := by
  have hp := measurePreserving_piEquivPiSubtypeProd (fun _ : Fin m => userLaw Γ)
    (fun j : Fin m => j ≠ i)
  have hfst := (measurePreserving_fst (μ := Measure.pi fun _ : Rival i => userLaw Γ)
    (ν := Measure.pi fun _ : {j : Fin m // ¬j ≠ i} => userLaw Γ)).comp hp
  have hm : Measurable (fun d : UserDraw n => effectiveBid d.1.2) :=
    (measurable_effectiveBid n).comp (measurable_snd.comp measurable_fst)
  have hbid := measurePreserving_pi (fun _ : Rival i => userLaw Γ)
    (fun _ : Rival i => (PayOnce.BidScaling.realBidLaw Γ : Measure ℝ))
    (fun _ => show MeasurePreserving (fun d : UserDraw n => effectiveBid d.1.2)
      (userLaw Γ) (PayOnce.BidScaling.realBidLaw Γ : Measure ℝ) from ⟨hm,rfl⟩)
  exact hbid.comp hfst

end FCAppendix.Bayes
