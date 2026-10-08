import FCAppendix.PayOnce.DummyFocalImpactBounds
import FCAppendix.PayOnce.PriceGoodEvent

namespace FCAppendix.PayOnce.DummyKernel
open MeasureTheory Set CommonList OwnImpact RareSuccessSlope PriceConcentration
open KernelTailEvent
open scoped BigOperators

noncomputable def activeWeight (p w : ℝ) : ℝ := if 0 < p ∧ p < 1 then w else 0

theorem measurable_activeWeight : Measurable (fun x : ℝ × ℝ => activeWeight x.1 x.2) :=
  Measurable.ite ((measurableSet_lt measurable_const measurable_fst).inter
    (measurableSet_lt measurable_fst measurable_const)) measurable_snd measurable_const

theorem weightedSlope_activeWeight (n : ℕ) (p w : ℝ) :
    weightedSlope n p (activeWeight p w) = weightedSlope n p w := by
  by_cases hp : 0 < p ∧ p < 1 <;> simp [activeWeight,weightedSlope,hp]

theorem activeWeight_mem_Icc {p w : ℝ} (hw : w ∈ Icc (0:ℝ) 1) :
    activeWeight p w ∈ Icc (0:ℝ) 1 := by
  by_cases hp : 0 < p ∧ p < 1 <;> simp [activeWeight,hp,hw]

theorem activeWeight_gap {p w κ : ℝ} (hκ : κ ≤ 1) (hw : κ ≤ 1-w) :
    κ ≤ 1-activeWeight p w := by
  by_cases hp : 0 < p ∧ p < 1 <;> simp [activeWeight,hp,hw,hκ]

theorem activeWeight_le_of_goodEvent
    {N n c : ℕ} (hN : 0 < N) (hn : 2 ≤ n)
    (r : Fin N → ℝ) {b ℓ u a z q w : ℝ}
    (hb : 0 < b) (hreg : RegularClearing n c r b)
    (hℓ : 0 < ℓ) (hu : 0 < u) (ha : u < a) (hz : z < (n:ℝ)*ℓ)
    (hq : 0 < q) (hg : r ∈ goodEvent n N c ℓ u a z q)
    (hweight : b*deriv (fun x => success n (allocation n c hn r x)) b =
      weightedSlope n (allocation n c hn r b) w) :
    activeWeight (allocation n c hn r b) w ≤ (n:ℝ)^3/(q*N) := by
  classical
  by_cases hi : 0 < allocation n c hn r b ∧ allocation n c hn r b < 1
  swap
  · simp only [activeWeight,if_neg hi]
    positivity
  rw [activeWeight,if_pos hi]
  obtain ⟨hr,T,hT,hcapA,_hzero,_hone,hclip0,hclip1⟩ := hreg
  have hcapacity := (goodEvent_capacity_le_active hn hℓ hg).trans (Nat.le_succ _)
  have hcap := hcapA
  rw [sum_active r hT,min_eq_left hcapacity] at hcap
  have hbracket := goodEvent_root_mem_Icc hn hℓ hu hg hT hcap
  have hp : allocation n c hn r b = kernel n b T :=
    AnalyticalKernel.allocation_eq_kernel hn (min_le_right c _) _ hr hb hT hcapA
  have hiT : kernel n b T ∈ Ioo (0:ℝ) 1 := by simpa only [hp,mem_Ioo] using hi
  let J := Finset.univ.filter fun j => r j ∈ Ioo a z
  let JA := Finset.univ.filter fun j : Active r => r j.val ∈ Ioo a z
  have hJAcard : JA.card = J.card := by
    apply Finset.card_bij (fun j _ => j.val)
    · intro j hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hj).2⟩
    · intro i _ j _ hij
      exact Subtype.ext hij
    · intro j hj
      have hwindow := (Finset.mem_filter.mp hj).2
      have hpositive : 0 < r j := hu.trans (ha.trans hwindow.1)
      exact ⟨⟨j,hpositive⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hwindow⟩,rfl⟩
  have hJA : ∀ j ∈ JA, kernel n (r j.val) T ∈ Ioo (0:ℝ) 1 := by
    intro j hj
    exact PriceInteriorBounds.kernel_interior_on_window hn hℓ hbracket ha hz
      (Finset.mem_filter.mp hj).2
  have hshare := focalWeight_le_of_interior_subset hn (fun j : Active r => r j.val) hr hb hT hiT JA hJA
    (show 0 < q*(N:ℝ) by positivity) (by simpa [hJAcard,J,Probability.sampleCount] using hg.2.2)
  have hd := focal_success_derivative_ownImpact hn (fun j : Active r => r j.val) hr
    (allocation n c hn r) hb hT hcapA hiT hclip0 hclip1
    (fun x hx => AnalyticalKernel.allocation_root hn (min_le_right c _) _ hr hx)
  rw [hp,weightedSlope,if_pos (show 0 < kernel n b T ∧ kernel n b T < 1 from hiT)] at hweight
  change b*deriv _ b = phi n (kernel n b T)*(1-_) at hd
  have hφ := AnalyticalKernel.phi_pos_interior hn hiT
  have hweq : w = focalWeight n b (kernel n b T)
      (rivalSensitivity n (fun j : Active r => r j.val) T) := by nlinarith [hweight,hd]
  exact hweq ▸ hshare

theorem exists_measurable_activeWeight_coverage_derivative
    {ι : Type*} [Fintype ι] {n c : ℕ} (hn : 2 ≤ n)
    (μ : Measure (ι → ℝ)) [IsProbabilityMeasure μ] {b : ℝ} (hb : 0 < b)
    (hreg : ∀ᵐ r ∂μ, RegularClearing n c r b) :
    ∃ w : (ι → ℝ) → ℝ, Measurable w ∧
      (∀ r, w r ∈ Icc (0:ℝ) 1) ∧
      (∀ r, 1/((n:ℝ)^3+1) ≤ 1-w r) ∧
      (∀ r, w r = activeWeight (allocation n c hn r b) (w r)) ∧
      (∀ᵐ r ∂μ, b*deriv (fun x => success n (allocation n c hn r x)) b =
        weightedSlope n (allocation n c hn r b) (w r)) ∧
      HasDerivAt (coverage n c hn μ)
        ((∫ r, weightedSlope n (allocation n c hn r b) (w r) ∂μ)/b) b := by
  obtain ⟨w,hm,hw,hgap,he,hd⟩ := exists_measurable_weight_coverage_derivative hn μ hb hreg
  let v := fun r => activeWeight (allocation n c hn r b) (w r)
  have hv : Measurable v := measurable_activeWeight.comp
    ((measurable_allocation_fixed_bid hn b).prodMk hm)
  refine ⟨v,hv,fun r => activeWeight_mem_Icc (hw r),?_,?_,?_,?_⟩
  · intro r
    exact activeWeight_gap (by apply (div_le_one (by positivity)).mpr; nlinarith [pow_nonneg (Nat.cast_nonneg n : (0:ℝ) ≤ n) 3]) (hgap r)
  · intro r
    dsimp only [v]
    by_cases hp : 0 < allocation n c hn r b ∧ allocation n c hn r b < 1 <;> simp [activeWeight,hp]
  · simpa only [v,weightedSlope_activeWeight] using he
  · simpa only [v,weightedSlope_activeWeight] using hd

end FCAppendix.PayOnce.DummyKernel
