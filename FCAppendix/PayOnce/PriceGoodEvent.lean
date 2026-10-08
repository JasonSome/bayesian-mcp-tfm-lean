import FCAppendix.PayOnce.PriceInteriorBounds
import FCAppendix.Probability.EmpiricalConcentration

namespace FCAppendix.PayOnce.PriceConcentration
open MeasureTheory ProbabilityTheory Set Filter Topology CommonList KernelTailEvent
open Probability PriceInteriorBounds
open scoped BigOperators

def goodEvent (n N c : ℕ) (ℓ u a z q : ℝ) : Set (Fin N → ℝ) :=
  {r | (c:ℝ) < ∑ j, kernel n (r j) ℓ ∧
    (∑ j, kernel n (r j) u) < (c:ℝ)-1 ∧
    q*(N:ℝ) ≤ (sampleCount (Ioo a z) r:ℝ)}

theorem measurableSet_goodEvent {n N c : ℕ} (hn : 2 ≤ n)
    {ℓ u a z q : ℝ} (hℓ : 0 < ℓ) (hu : 0 < u) :
    MeasurableSet (goodEvent n N c ℓ u a z q) := by
  have hs {T : ℝ} (hT : 0 < T) : Measurable
      (fun r : Fin N → ℝ => ∑ j, kernel n (r j) T) :=
    Finset.measurable_sum _ (fun j _ =>
      (continuous_kernel_bid hn hT).measurable.comp (measurable_pi_apply j))
  have hm : Measurable (fun r : Fin N → ℝ => (sampleCount (Ioo a z) r:ℝ)) :=
    (measurable_of_countable (fun k : ℕ => (k:ℝ))).comp
      (measurable_sampleCount (Ioo a z) measurableSet_Ioo N)
  exact (measurableSet_lt measurable_const (hs hℓ)).inter
    ((measurableSet_lt (hs hu) measurable_const).inter
      (measurableSet_le measurable_const hm))

theorem goodEvent_capacity_le_active {n N c : ℕ} (hn : 2 ≤ n)
    {ℓ u a z q : ℝ} (hℓ : 0 < ℓ) {r : Fin N → ℝ}
    (hr : r ∈ goodEvent n N c ℓ u a z q) :
    c ≤ Fintype.card (DummyKernel.Active r) := by
  have hh := hr.1.trans_le (DummyKernel.sum_kernel_le_active_card hn r hℓ)
  exact (Nat.cast_lt.mp hh).le

theorem goodEvent_root_mem_Icc {n N c : ℕ} (hn : 2 ≤ n)
    {ℓ u a z q b R : ℝ} (hℓ : 0 < ℓ) (hu : 0 < u)
    {r : Fin N → ℝ} (hr : r ∈ goodEvent n N c ℓ u a z q)
    (hR : 0 < R) (hcap : kernel n b R+∑ j, kernel n (r j) R = (c:ℝ)) :
    R ∈ Icc ℓ u := by
  constructor
  · by_contra h
    have hRℓ : R ≤ ℓ := (lt_of_not_ge h).le
    have hs : (∑ j, kernel n (r j) ℓ) ≤ ∑ j, kernel n (r j) R :=
      Finset.sum_le_sum (fun j _ => kernel_antitone_price hn hR hℓ hRℓ)
    have hp := (kernel_bounds hn hR b).1
    linarith [hr.1]
  · by_contra h
    have huR : u ≤ R := (lt_of_not_ge h).le
    have hs : (∑ j, kernel n (r j) R) ≤ ∑ j, kernel n (r j) u :=
      Finset.sum_le_sum (fun j _ => kernel_antitone_price hn hu hR huR)
    have hp := (kernel_bounds hn hR b).2
    linarith [hr.2.1]

theorem goodEvent_compl_le {n N c : ℕ} (hn : 2 ≤ n) (hN : 0 < N)
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {ℓ u a z q δlo δhi : ℝ} (hℓ : 0 < ℓ) (hu : 0 < u)
    (hq : 0 ≤ q) (hδlo : 0 ≤ δlo) (hδhi : 0 ≤ δhi)
    (hlo : (c:ℝ)/(N:ℝ) ≤ (∫ b, kernel n b ℓ ∂μ)-δlo)
    (hhi : (∫ b, kernel n b u ∂μ)+δhi ≤ ((c:ℝ)-1)/(N:ℝ))
    (hmass : 2*q ≤ μ.real (Ioo a z)) :
    (Measure.pi (fun _ : Fin N => μ)).real (goodEvent n N c ℓ u a z q)ᶜ ≤
      Real.exp (-2*(N:ℝ)*δlo^2)+Real.exp (-2*(N:ℝ)*δhi^2)+
        Real.exp (-2*(N:ℝ)*q^2) := by
  let P := Measure.pi (fun _ : Fin N => μ)
  let E₀ := {r : Fin N → ℝ | δlo ≤ (∫ b, kernel n b ℓ ∂μ)-(∑ j, kernel n (r j) ℓ)/(N:ℝ)}
  let E₁ := {r : Fin N → ℝ | δhi ≤ (∑ j, kernel n (r j) u)/(N:ℝ)-(∫ b, kernel n b u ∂μ)}
  let E₂ := {r : Fin N → ℝ | (sampleCount (Ioo a z) r:ℝ) ≤ (N:ℝ)*(μ.real (Ioo a z)-q)}
  have hNR : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hsub : (goodEvent n N c ℓ u a z q)ᶜ ⊆ (E₀ ∪ E₁) ∪ E₂ := by
    intro r hr
    by_cases hl : (c:ℝ) < ∑ j, kernel n (r j) ℓ
    · by_cases hh : (∑ j, kernel n (r j) u) < (c:ℝ)-1
      · have hc : (sampleCount (Ioo a z) r:ℝ) < q*(N:ℝ) := by
          by_contra hc
          exact hr ⟨hl,hh,le_of_not_gt hc⟩
        right
        dsimp only [E₂,mem_setOf_eq]
        have hmul := mul_le_mul_of_nonneg_left hmass hNR.le
        nlinarith
      · left; right
        dsimp only [E₁,mem_setOf_eq]
        have hd := div_le_div_of_nonneg_right (le_of_not_gt hh) hNR.le
        linarith
    · left; left
      dsimp only [E₀,mem_setOf_eq]
      have hd := div_le_div_of_nonneg_right (le_of_not_gt hl) hNR.le
      linarith
  have he₀ : P.real E₀ ≤ Real.exp (-2*(N:ℝ)*δlo^2) :=
    iid_empiricalMean_lower_tail_le μ (continuous_kernel_bid hn hℓ).measurable.aemeasurable
      (Eventually.of_forall fun b => kernel_bounds hn hℓ b) N hN hδlo
  have he₁ : P.real E₁ ≤ Real.exp (-2*(N:ℝ)*δhi^2) :=
    iid_empiricalMean_upper_tail_le μ (continuous_kernel_bid hn hu).measurable.aemeasurable
      (Eventually.of_forall fun b => kernel_bounds hn hu b) N hN hδhi
  have he₂ : P.real E₂ ≤ Real.exp (-2*(N:ℝ)*q^2) :=
    iid_indicator_lower_tail_le μ (Ioo a z) measurableSet_Ioo N hN hq
  exact (measureReal_mono hsub).trans
    ((measureReal_union_le (μ := P) (E₀ ∪ E₁) E₂).trans
      ((add_le_add (measureReal_union_le (μ := P) E₀ E₁) le_rfl).trans
        (add_le_add (add_le_add he₀ he₁) he₂)))

theorem goodEvent_compl_le_exponential {n N c : ℕ} (hn : 2 ≤ n) (hN : 0 < N)
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {ℓ u a z q δlo δhi d : ℝ} (hℓ : 0 < ℓ) (hu : 0 < u)
    (hq : 0 ≤ q) (hδlo : 0 ≤ δlo) (hδhi : 0 ≤ δhi)
    (hlo : (c:ℝ)/(N:ℝ) ≤ (∫ b, kernel n b ℓ ∂μ)-δlo)
    (hhi : (∫ b, kernel n b u ∂μ)+δhi ≤ ((c:ℝ)-1)/(N:ℝ))
    (hmass : 2*q ≤ μ.real (Ioo a z))
    (hdlo : d ≤ 2*δlo^2) (hdhi : d ≤ 2*δhi^2) (hdq : d ≤ 2*q^2) :
    (Measure.pi (fun _ : Fin N => μ)).real (goodEvent n N c ℓ u a z q)ᶜ ≤
      3*Real.exp (-d*(N:ℝ)) := by
  have he {v : ℝ} (hv : d ≤ 2*v^2) :
      Real.exp (-2*(N:ℝ)*v^2) ≤ Real.exp (-d*(N:ℝ)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right hv (Nat.cast_nonneg N : (0:ℝ) ≤ N)]
  have hh := goodEvent_compl_le hn hN μ hℓ hu hq hδlo hδhi hlo hhi hmass
  have hh' := hh.trans (add_le_add (add_le_add (he hdlo) (he hdhi)) (he hdq))
  linarith

end FCAppendix.PayOnce.PriceConcentration
