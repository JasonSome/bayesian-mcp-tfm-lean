import FCAppendix.PayOnce.InactiveCentralActualProfiles

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology CommonList Real
open PayOnce PayOnce.CompactifiedBidLaws PayOnce.DummyKernel Probability
variable {M C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem payOnce_inactive_central_interval_regular
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ)
    (hlocal : GaussianParameters.LocalFullSupport (F.map (fun v => max (v-g) 0))
      (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ))
    (P : ℕ → ℝ → Prop) (hP : ∀ t, ∀ᵐ v ∂F, P t v)
    (l r : ℕ → ℝ) {x : ℝ} (hl : Tendsto l atTop (𝓝 x)) (hr : Tendsto r atTop (𝓝 x))
    (hlr : ∀ᶠ t in atTop, l t < r t) :
    ∀ᶠ t in atTop, ∃ y ∈ Ioo (l t) (r t),
      P t (inactiveCentralValue M C F (k+1) g ρ y t) := by
  let L := Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ
  have hL : 0 < L := (payOnce_inactive_eventual_pure_bid_limit Γ B F g ρ h).1
  obtain ⟨δ,hδ,hlocal⟩ := hlocal
  have hll := payOnce_inactive_central_value_tendsto Γ B F g ρ h l hl
  have hrr := payOnce_inactive_central_value_tendsto Γ B F g ρ h r hr
  filter_upwards [hll.eventually (Ioi_mem_nhds (by linarith : L-δ < L)),
    hrr.eventually_lt_const (by linarith : L < L+δ),hll.eventually (Ioi_mem_nhds hL),
    h.population_grows.eventually_gt_atTop 0,hlr] with t hlt hrt hpos hm hlr
  have hs := payOnce_inactive_gaussian_scale_pos Γ B F g ρ h
    ⟨δ,hδ,hlocal⟩ hm
  let a := inactiveCentralValue M C F (k+1) g ρ (l t) t-g
  let b := inactiveCentralValue M C F (k+1) g ρ (r t) t-g
  have hab : a < b := by
    dsimp only [a,b,inactiveCentralValue]
    nlinarith
  have hmass := hlocal a b hlt hab hrt
  have hmap : Measurable (fun v : ℝ => max (v-g) 0) :=
    (measurable_id.sub_const g).max measurable_const
  rw [Measure.map_apply hmap measurableSet_Ioo] at hmass
  obtain ⟨v,hv,hPv⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hmass.ne'
    (ae_restrict_of_ae (hP t))
  change a < max (v-g) 0 ∧ max (v-g) 0 < b at hv
  have hvpos : 0 < v-g := by
    by_contra hn
    rw [max_eq_right (le_of_not_gt hn)] at hv
    exact (lt_trans hpos hv.1).false
  have hv' : a < v-g ∧ v-g < b := by simpa only [max_eq_left hvpos.le] using hv
  let y := (v-g-inactiveValuePrice M C F (k+1) g t)/inactiveGaussianScale M F (k+1) g ρ t
  have hy : inactiveCentralValue M C F (k+1) g ρ y t=v := by
    dsimp only [inactiveCentralValue,y]
    rw [mul_div_cancel₀ _ hs.ne']
    ring
  refine ⟨y,⟨?_,?_⟩,by rwa [hy]⟩
  · apply (lt_div_iff₀ hs).mpr
    dsimp only [a,inactiveCentralValue] at hv'
    linarith [hv'.1]
  · apply (div_lt_iff₀ hs).mpr
    dsimp only [b,inactiveCentralValue] at hv'
    linarith [hv'.2]

theorem payOnce_inactive_central_regular_brackets
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ)
    (hlocal : GaussianParameters.LocalFullSupport (F.map (fun v => max (v-g) 0))
      (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ))
    (P : ℕ → ℝ → Prop) (hP : ∀ t, ∀ᵐ v ∂F, P t v)
    (x : ℕ → ℝ) {x₀ : ℝ} (hx : Tendsto x atTop (𝓝 x₀)) :
    ∃ l r : ℕ → ℝ, Tendsto l atTop (𝓝 x₀) ∧ Tendsto r atTop (𝓝 x₀) ∧
      ∀ᶠ t in atTop, l t < x t ∧ x t < r t ∧
        P t (inactiveCentralValue M C F (k+1) g ρ (l t) t) ∧
        P t (inactiveCentralValue M C F (k+1) g ρ (r t) t) := by
  classical
  let d := fun t : ℕ => 1/((t:ℝ)+1)
  have hd t : 0 < d t := by dsimp only [d]; positivity
  have hdlim : Tendsto d atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hleft := payOnce_inactive_central_interval_regular Γ B F g ρ h hlocal P hP
    (fun t => x t-d t) x (by simpa using hx.sub hdlim) hx
    (.of_forall fun t => by linarith [hd t])
  have hright := payOnce_inactive_central_interval_regular Γ B F g ρ h hlocal P hP
    x (fun t => x t+d t) hx (by simpa using hx.add hdlim)
    (.of_forall fun t => by linarith [hd t])
  let Q := fun t y => P t (inactiveCentralValue M C F (k+1) g ρ y t)
  let l := fun t => if ht : ∃ y ∈ Ioo (x t-d t) (x t), Q t y then ht.choose else x t
  let r := fun t => if ht : ∃ y ∈ Ioo (x t) (x t+d t), Q t y then ht.choose else x t
  have hls t : x t-d t ≤ l t ∧ l t ≤ x t := by
    dsimp only [l]
    split_ifs with ht
    · exact ⟨ht.choose_spec.1.1.le,ht.choose_spec.1.2.le⟩
    · exact ⟨by linarith [hd t],le_rfl⟩
  have hrs t : x t ≤ r t ∧ r t ≤ x t+d t := by
    dsimp only [r]
    split_ifs with ht
    · exact ⟨ht.choose_spec.1.1.le,ht.choose_spec.1.2.le⟩
    · exact ⟨le_rfl,by linarith [hd t]⟩
  refine ⟨l,r,?_,?_,?_⟩
  · exact tendsto_of_tendsto_of_tendsto_of_le_of_le (by simpa using hx.sub hdlim) hx
      (fun t => (hls t).1) (fun t => (hls t).2)
  · exact tendsto_of_tendsto_of_tendsto_of_le_of_le hx (by simpa using hx.add hdlim)
      (fun t => (hrs t).1) (fun t => (hrs t).2)
  · filter_upwards [hleft,hright] with t hl hr
    have hl' : l t=hl.choose := dif_pos hl
    have hr' : r t=hr.choose := dif_pos hr
    rw [hl',hr']
    exact ⟨hl.choose_spec.1.2,hr.choose_spec.1.1,hl.choose_spec.2,hr.choose_spec.2⟩

end FCAppendix.Bayes
