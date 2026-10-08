import FCAppendix.PayOnce.ProfilePriceCLT
import FCAppendix.PayOnce.PriceConcentration

namespace FCAppendix.PayOnce.PriceConcentration
open MeasureTheory ProbabilityTheory Set Filter Topology CommonList KernelTailEvent
open DummyKernel
open scoped BigOperators

theorem profilePrice_tail_le_bad_add_gaussian {n M c : ℕ} (hn : 2 ≤ n) (hM : 0 < M)
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {ℓ u a z q T ε : ℝ} (hℓ : 0 < ℓ) (hT : T ∈ Icc ℓ u)
    (ha : u < a) (haz : a < z) (hz : z < (n:ℝ)*ℓ) (hq : 0 < q)
    (hbias : |(∫ b, kernel n b T ∂μ)-(c:ℝ)/(M:ℝ)| ≤ 1/(M:ℝ))
    (hε : 0 ≤ ε) :
    (Measure.pi (fun _ : Fin M => μ)).real {r | ε ≤ |profilePrice n c hn hM r-T|} ≤
      2*(Measure.pi (fun _ : Fin M => μ)).real (goodEvent n M c ℓ u a z q)ᶜ+
        (2*Real.exp 8)*Real.exp (-(M:ℝ)*ε^2/(2*((n:ℝ)*z/q)^2)) := by
  classical
  let E := goodEvent n M c ℓ u a z q
  let P := Measure.pi (fun _ : Fin M => μ)
  let R := fun r : Fin M → ℝ => if r ∈ E then profilePrice n c hn hM r else focalPrice n c hn 1 r
  let b := fun r : Fin M → ℝ => if r ∈ E then (0:ℝ) else 1
  have hR (r : Fin M → ℝ) : 0 < R r := by
    by_cases hr : r ∈ E
    · simpa only [R,if_pos hr] using (profilePrice_spec hn hM r).1
    · simpa only [R,if_neg hr] using (focalPrice_spec hn 1 r zero_lt_one).1
  have hcap (r : Fin M → ℝ) : kernel n (b r) (R r)+∑ j, kernel n (r j) (R r) =
      (min c (Fintype.card (Active r)+1):ℕ) := by
    by_cases hr : r ∈ E
    · have hc := goodEvent_capacity_le_active hn hℓ hr
      have hh := (profilePrice_spec (c := c) hn hM r).2.2
      rw [Nat.min_eq_left hc] at hh
      simp only [b,R,if_pos hr,Nat.min_eq_left (hc.trans (Nat.le_succ _))]
      rw [kernel_of_le n (profilePrice_spec (c := c) hn hM r).1.le,zero_add]
      exact hh
    · simpa only [b,R,if_neg hr] using (focalPrice_spec (c := c) hn 1 r zero_lt_one).2.1
  have hh := price_tail_le_bad_add_gaussian hn hM μ hℓ hT ha haz hz hq b R hR hcap hbias hε
  have hsub : {r : Fin M → ℝ | ε ≤ |profilePrice n c hn hM r-T|} ⊆
      Eᶜ ∪ {r | ε ≤ |R r-T|} := by
    intro r hr
    by_cases he : r ∈ E
    · exact Or.inr (by simpa only [mem_setOf_eq,R,if_pos he] using hr)
    · exact Or.inl he
  have hu := (measureReal_mono (μ := P) hsub).trans (measureReal_union_le _ _)
  change P.real {r | ε ≤ |profilePrice n c hn hM r-T|} ≤ _
  change P.real {r | ε ≤ |R r-T|} ≤ P.real Eᶜ+_ at hh
  linarith

end FCAppendix.PayOnce.PriceConcentration
