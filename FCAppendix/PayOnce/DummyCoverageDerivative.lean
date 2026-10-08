import FCAppendix.PayOnce.DummyNullClipping
import FCAppendix.PayOnce.DummyInterimKernel

namespace FCAppendix.PayOnce.DummyKernel
open MeasureTheory Filter Topology Set CommonList OwnImpact
open scoped BigOperators
variable {ι : Type*} [Fintype ι]

def RegularClearing (n c : ℕ) (r : ι → ℝ) (b : ℝ) : Prop :=
  AnalyticalKernel.RegularClearing n (min c (Fintype.card (Active r)+1))
    (fun j : Active r => r j.val) b

theorem differentiableAt_allocation_of_regular {n c : ℕ} (hn : 2 ≤ n)
    (r : ι → ℝ) {b : ℝ} (hb : 0 < b) (hreg : RegularClearing n c r b) :
    DifferentiableAt ℝ (allocation n c hn r) b :=
  AnalyticalKernel.differentiableAt_allocation_of_regular hn (min_le_right _ _) _ hb hreg

theorem active_card_option (r : ι → ℝ) {b : ℝ} (hb : 0 < b) :
    Fintype.card (Active ((MeasurableEquiv.piOptionEquivProd (fun _ : Option ι => ℝ)).symm (r,b))) =
      Fintype.card (Active r)+1 := by
  classical
  let d : Option ι → ℝ := (MeasurableEquiv.piOptionEquivProd (fun _ : Option ι => ℝ)).symm (r,b)
  have hd : (∑ j : Option ι, if 0 < d j then (1:ℝ) else 0) = (Fintype.card (Active d):ℝ) := by
    simp [Active,Fintype.card_subtype]
  have hr : (∑ j : ι, if 0 < r j then (1:ℝ) else 0) = (Fintype.card (Active r):ℝ) := by
    simp [Active,Fintype.card_subtype]
  have hh : (Fintype.card (Active d):ℝ) = (Fintype.card (Active r):ℝ)+1 := by
    rw [← hd,← hr,Fintype.sum_option]
    change (if 0 < b then (1:ℝ) else 0) + (∑ j : ι, if 0 < r j then (1:ℝ) else 0) = _
    rw [if_pos hb]
    ring
  exact_mod_cast hh

theorem ae_regularClearing_prod (G : Measure ℝ) [IsProbabilityMeasure G]
    (hatom : ∀ b : ℝ, 0 < b → G {b} = 0) {n c : ℕ} (hn : 2 ≤ n) :
    ∀ᵐ z ∂G.prod (Measure.pi (fun _ : ι => G)),
      0 < z.1 → RegularClearing n c z.2 z.1 := by
  classical
  let e := MeasurableEquiv.piOptionEquivProd (fun _ : Option ι => ℝ)
  have hfull := DummyNullClipping.ae_regularRoot (ι := Option ι) (c := c) G hatom hn
  rw [← Measure.pi_map_piOptionEquivProd (fun _ : Option ι => G)] at hfull
  have hp := ae_of_ae_map e.symm.measurable.aemeasurable hfull
  have hreg : ∀ᵐ z ∂(Measure.pi (fun _ : ι => G)).prod G,
      0 < z.2 → RegularClearing n c z.1 z.2 := by
    filter_upwards [hp] with z hz hb
    obtain ⟨L,hL,hcap,hz0,hz1⟩ := hz
    refine ⟨fun j => j.property,L,hL,?_,hz0 none,hz1 none,
      fun j => hz0 (some j.val),fun j => hz1 (some j.val)⟩
    rw [sum_active z.1 hL]
    change kernel n (e.symm z none) L + ∑ j, kernel n (e.symm z (some j)) L = _
    have hcard := active_card_option z.1 hb
    rw [hcard] at hcap
    simpa only [Fintype.sum_option,add_comm] using hcap
  have hswap : ∀ᵐ z ∂G.prod (Measure.pi (fun _ : ι => G)),
      0 < z.1 → RegularClearing n c z.2 z.1 := by
    have hh := hreg
    rw [← Measure.prod_swap] at hh
    exact ae_of_ae_map measurable_swap.aemeasurable hh
  exact hswap

theorem ae_regularClearing (G : Measure ℝ) [IsProbabilityMeasure G]
    (hatom : ∀ b : ℝ, 0 < b → G {b} = 0) {n c : ℕ} (hn : 2 ≤ n) :
    ∀ᵐ b ∂G, 0 < b → ∀ᵐ r ∂Measure.pi (fun _ : ι => G), RegularClearing n c r b := by
  filter_upwards [Measure.ae_ae_of_ae_prod (ae_regularClearing_prod (ι := ι) (c := c) G hatom hn)]
    with b hb hpos
  exact hb.mono fun r hr => hr hpos

theorem aestronglyMeasurable_success_deriv {n c : ℕ} (hn : 2 ≤ n)
    (μ : Measure (ι → ℝ)) {b : ℝ} (hb : 0 < b)
    (hreg : ∀ᵐ r ∂μ, RegularClearing n c r b) :
    AEStronglyMeasurable (fun r => deriv (fun x => success n (allocation n c hn r x)) b) μ := by
  let F : ℝ → (ι → ℝ) → ℝ := fun x r => success n (allocation n c hn r x)
  let δ : ℕ → ℝ := fun j => 1/((j:ℝ)+1)
  have hδ (j : ℕ) : 0 < δ j := by dsimp only [δ]; positivity
  have hδlim : Tendsto δ atTop (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Filter.Eventually.of_forall fun j => (hδ j).ne'⟩
  apply aestronglyMeasurable_of_tendsto_ae atTop
    (f := fun j r => (F (b+δ j) r-F b r)/δ j)
  · intro j
    exact ((((continuous_success n).measurable.comp (measurable_allocation_fixed_bid hn _)).sub
      ((continuous_success n).measurable.comp (measurable_allocation_fixed_bid hn _))).div_const (δ j)).aestronglyMeasurable
  · filter_upwards [hreg] with r hr
    have hp := differentiableAt_allocation_of_regular hn r hb hr
    have hs : DifferentiableAt ℝ (fun x => F x r) b :=
      (differentiableAt_const (1:ℝ)).sub (((differentiableAt_const (1:ℝ)).sub hp).pow n)
    have hh := hs.hasDerivAt.tendsto_slope_zero.comp hδlim
    simpa only [Function.comp_def,F,smul_eq_mul,div_eq_mul_inv,mul_comm] using hh

theorem hasDerivAt_coverage_of_regular {n c : ℕ} (hn : 2 ≤ n)
    (μ : Measure (ι → ℝ)) [IsProbabilityMeasure μ] {b : ℝ} (hb : 0 < b)
    (hreg : ∀ᵐ r ∂μ, RegularClearing n c r b) :
    Integrable (fun r => deriv (fun x => success n (allocation n c hn r x)) b) μ ∧
      HasDerivAt (coverage n c hn μ)
        (∫ r, deriv (fun x => success n (allocation n c hn r x)) b ∂μ) b := by
  let F : ℝ → (ι → ℝ) → ℝ := fun x r => success n (allocation n c hn r x)
  have hhalf : 0 < b/2 := by linarith
  apply hasDerivAt_integral_of_dominated_loc_of_lip
    (F := F) (s := Ioi (b/2)) (bound := fun _ : ι → ℝ => (n:ℝ)^2/(b/2))
    (Ioi_mem_nhds (by linarith : b/2 < b))
  · exact Filter.Eventually.of_forall fun x =>
      ((continuous_success n).measurable.comp (measurable_allocation_fixed_bid hn x)).aestronglyMeasurable
  · exact integrable_success_allocation hn μ b
  · exact aestronglyMeasurable_success_deriv hn μ hb hreg
  · exact Filter.Eventually.of_forall fun r =>
      (focal_success_lipschitzOn hn r _ hhalf
        (fun x hx => allocation_root hn r hx)).mono Ioi_subset_Ici_self
  · exact integrable_const _
  · filter_upwards [hreg] with r hr
    have hp := differentiableAt_allocation_of_regular hn r hb hr
    have hs : DifferentiableAt ℝ (fun x => F x r) b :=
      (differentiableAt_const (1:ℝ)).sub (((differentiableAt_const (1:ℝ)).sub hp).pow n)
    exact hs.hasDerivAt

theorem ae_hasDerivAt_coverage (G : Measure ℝ) [IsProbabilityMeasure G]
    (hatom : ∀ b : ℝ, 0 < b → G {b} = 0) {n c : ℕ} (hn : 2 ≤ n) :
    ∀ᵐ b ∂G, 0 < b →
      HasDerivAt (coverage n c hn (Measure.pi fun _ : ι => G))
        (deriv (coverage n c hn (Measure.pi fun _ : ι => G)) b) b := by
  filter_upwards [ae_regularClearing (ι := ι) (c := c) G hatom hn] with b hb hpos
  exact (hasDerivAt_coverage_of_regular hn _ hpos (hb hpos)).2.differentiableAt.hasDerivAt

end FCAppendix.PayOnce.DummyKernel
