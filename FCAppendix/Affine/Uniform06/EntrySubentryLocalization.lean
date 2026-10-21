import FCAppendix.Affine.Uniform06.EntryGoodKernelBounds
import FCAppendix.Affine.Uniform06.FiniteMean

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.EntrySubentryLocalization

open MeasureTheory Set Filter Topology LowBody
open FCAppendix.Affine.Uniform07 FCAppendix.Affine.ClippedResidual
open EntryConstructedSource EntryConstructedSource.EarlyArray EntryFiniteConstructor
open EntryProducedMoments EntryGoodKernelBounds EntryEarlySourceLimits
open EntryLiteralCanonicalTransfer EntryPopulationMargins
open scoped BigOperators

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {i : Row} (s : EarlyArray μ i)

theorem fixed_price_geometry {z : ℝ} (hz : z∈Ioo (lowerPrice i) (entry i)) :
    0< z ∧ ReceiptGap.threshold i< z ∧ z< ReceiptGap.cap i ∧
    z/cutoff i∈Icc (1/2:ℝ) (x i) ∧
    0<(1-x i)*(entry i-z) ∧ (1-x i)*(entry i-z)< cutoff i/1000 := by
  have ht := cutoff_pos i
  have hx : (7/10:ℝ)≤ x i ∧ x i≤3/4 := by cases i <;> norm_num [x,xQ]
  have hrec := ReceiptGap.receipt_entry_margin i
  have hU := ReceiptGap.entry_below_cap i
  have hξ : 0<1-x i := by linarith
  have hlow : entry i-cutoff i/1000< z := hz.1
  have hz0 : 0< z := by unfold entry at hlow; nlinarith
  refine ⟨hz0,by unfold lowerPrice at hz; linarith,hz.2.trans hU,⟨?_,?_⟩,
    mul_pos hξ (sub_pos.mpr hz.2),?_⟩
  · apply (le_div_iff₀ ht).mpr
    unfold entry at hlow
    nlinarith
  · apply (div_le_iff₀ ht).mpr
    simpa only [entry,mul_comm] using hz.2.le
  · have hδ : 0< entry i-z := sub_pos.mpr hz.2
    have h1 : (1-x i)*(entry i-z)≤ entry i-z := by nlinarith
    linarith

theorem eventual_fixed_mean_gap {z : ℝ} (hz : z∈Ioo (lowerPrice i) (entry i)) :
    ∀ᶠ m in atTop,rho+((1-x i)*(entry i-z))/2≤ RawMixedSource.mean i (s.jointLaw m) z := by
  let d := (1-x i)*(entry i-z)
  let a := d/4
  let e := xi i*(z/cutoff i)*d/4
  have hgeo := fixed_price_geometry (i := i) hz
  have hd : 0< d := hgeo.2.2.2.2.1
  have ht := cutoff_pos i
  have ha : 0< a := by dsimp [a]; positivity
  have hzn : 0< z/cutoff i := div_pos hgeo.1 ht
  have he : 0< e := by dsimp [e]; have := xi_pos i; positivity
  have haT : entry i+a≤ cutoff i := by
    have hx : x i≤3/4 := by cases i <;> norm_num [x,xQ]
    have hh := mul_le_mul_of_nonneg_right hx ht.le
    have hsmall := hgeo.2.2.2.2.2
    dsimp [a,d]
    unfold entry at *
    nlinarith
  filter_upwards [s.active_closed a ha e he] with m hm
  have hgraph : ∀ᵐ p ∂s.jointLaw m,p.1∈Ioc (entry i+a) (cutoff i) →
      |p.2-ActiveGraphComponent.activeBid i p.1|≤ e := by
    apply (ae_map_iff (s.value_measurable.prodMk (s.bid_measurable m)).aemeasurable
      (by unfold ActiveGraphComponent.activeBid; measurability)).mpr
    filter_upwards [hm] with ω hω hv
    exact (hω ⟨hv.1.le,hv.2⟩).le
  have hh := FiniteMean.finite_subentry_mean_lower i (s.jointLaw m) (s.value_marginal m)
    ha haT he.le hgeo.2.2.2.1 hgraph
  have hzform : z/cutoff i*cutoff i=z := div_mul_cancel₀ _ ht.ne'
  have heform : e/(xi i*(z/cutoff i))=d/4 := by
    dsimp only [e]
    field_simp [(xi_pos i).ne',hzn.ne',hgeo.1.ne']
  rw [hzform,heform] at hh
  have hid := RawMixedSource.integral_source_test i (s.jointLaw m) hgeo.1 Prod.fst measurable_fst
  change RawMixedSource.mean i (s.jointLaw m) z=_ at hid
  rw [← hid] at hh
  dsimp only [a,d] at hh
  linarith

theorem all_bids_below_fixed_price {z : ℝ} (hz : z∈Ioo (lowerPrice i) (entry i)) :
    ∃ κ : ℝ,0<κ ∧ ∀ᶠ m in atTop,∀ b∈Icc (0:ℝ) z,
      first s m b≤ Real.exp (-κ*((s.population m-1:ℕ):ℝ)) := by
  let d := (1-x i)*(entry i-z)
  let τ := d/4
  let κ := 2*τ^2
  have hgeo := fixed_price_geometry (i := i) hz
  have hd : 0< d := hgeo.2.2.2.2.1
  have hτ : 0<τ := by dsimp [τ]; positivity
  have hκ : 0<κ := by dsimp [κ]; positivity
  have hN := PhysicalRates.rivals_tendsto.comp s.population_tendsto
  have hNlarge := (tendsto_natCast_atTop_atTop.comp hN).const_mul_atTop hτ
  have ht := cutoff_pos i
  have hbEntry : entry i∈band i := by
    unfold band SourcePrefixConstructor.radius
    constructor <;> linarith
  have hhi : ∀ᶠ m in atTop,z≤(s.guards m).multiplier+(s.guards m).radius := by
    filter_upwards [s.multiplier_tendsto.eventually_const_lt hz.2] with m hm
    have ha : 0≤(s.guards m).radius := by rw [(s.literal m).radius_eq]; unfold SourcePrefixConstructor.radius; positivity
    linarith
  refine ⟨κ,hκ,?_⟩
  filter_upwards [s.eventually_inputs,eventual_fixed_mean_gap s hz,
    hNlarge.eventually_ge_atTop 1,hhi] with m hm hmean hlarge hzhi
  let g := normalizeCount (s.guards m)
  have h := hm.2 (entry i) hbEntry
  have hqz : first s m z≤ Real.exp (-κ*((s.population m-1:ℕ):ℝ)) := by
    by_cases hzl : z≤(s.guards m).multiplier-(s.guards m).radius
    · have hh := original_below_lower_zero i (s.jointLaw m) g h hzl
      have hz0 : first s m z=0 := by
        simpa only [first,g,canonicalGoodMarginal_normalize] using hh
      rw [hz0]
      exact (Real.exp_pos _).le
    · have hzb : z∈Icc (g.multiplier-g.radius) (g.multiplier+g.radius) :=
        ⟨(lt_of_not_ge hzl).le,hzhi⟩
      have hzcap : z≤ ReceiptGap.cap i := hgeo.2.2.1.le
      have hh := Inputs.at_bid h hzb hzcap hgeo.2.1.le
      have hn : (0:ℝ)<((s.population m-1:ℕ):ℝ) := Nat.cast_pos.mpr h.rivals_pos
      have hf := (abs_le.mp (EntryFiniteConstructor.floor_error (by omega : 2≤ s.population m))).2
      have hc : (capacity (s.population m):ℝ)/((s.population m-1:ℕ):ℝ)+τ≤
          RawMixedSource.mean i (s.jointLaw m) z := by
        have hmul := mul_le_mul_of_nonneg_right hmean hn.le
        change (rho+d/2)*((s.population m-1:ℕ):ℝ)≤
          RawMixedSource.mean i (s.jointLaw m) z*((s.population m-1:ℕ):ℝ) at hmul
        change 1≤τ*((s.population m-1:ℕ):ℝ) at hlarge
        have hC : (capacity (s.population m):ℝ)/((s.population m-1:ℕ):ℝ)≤
            RawMixedSource.mean i (s.jointLaw m) z-τ := by
          apply (div_le_iff₀ hn).mpr
          change rho+d/2≤ RawMixedSource.mean i (s.jointLaw m) z at hmean
          dsimp only [τ] at *
          nlinarith
        linarith
      have htail := original_good_lower_tail i (s.jointLaw m) g hh (s.cap m) hτ.le hc
      simpa [first,g,κ,mul_assoc,mul_comm,mul_left_comm] using htail
  have hmono := original_good_monotone i (s.jointLaw m) (s.joint_nonnegative m) g h (s.cap m)
  intro b hb
  have hh := hmono ⟨hb.1,hb.2.trans hzhi⟩ ⟨hgeo.1.le,hzhi⟩ hb.2
  have hq : first s m b≤ first s m z := by
    simpa only [first,g,canonicalGoodMarginal_normalize] using hh
  exact hq.trans hqz

end FCAppendix.Affine.Uniform06.EntrySubentryLocalization
