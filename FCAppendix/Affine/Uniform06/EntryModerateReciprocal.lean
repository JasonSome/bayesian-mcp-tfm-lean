import FCAppendix.Affine.Uniform06.EntryRelativeWeight

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.EntryModerateReciprocal
open MeasureTheory ProbabilityTheory Set Filter Topology LowBody
open FCAppendix.Affine.Uniform07 FCAppendix.ExponentialTilt
open EntryReciprocalLimit EntryEarlySourceLimits EntryRawTiltedFiber
open EntryModerateProfile EntryRawModerate EntryEmpiricalRatio
open scoped BigOperators

lemma rawReciprocal_nonneg {z : ℝ} (hz : 0 < z) (r : RowRival) : 0 ≤ rawReciprocal z r := by
  unfold rawReciprocal RivalGood.lowerTest
  split_ifs
  · exact ReciprocalSecantBounds.reciprocalTerm_nonneg hz
  · rfl

def test (lo z : ℝ) (r : RowRival) : ℝ := lo*rawReciprocal z r

lemma test_measurable (lo z : ℝ) : Measurable (test lo z) := (measurable_rawReciprocal z).const_mul lo

lemma test_unit {lo z : ℝ} (hlo : 0 < lo) (hz : lo ≤ z) (r : RowRival) :
    test lo z r∈Icc (0:ℝ) 1 := by
  have hn := rawReciprocal_nonneg (hlo.trans_le hz) r
  have hb := rawReciprocal_bound hlo hz r
  rw [abs_of_nonneg hn] at hb
  refine ⟨mul_nonneg hlo.le hn,?_⟩
  have hm := mul_le_mul_of_nonneg_left hb hlo.le
  simpa [test,hlo.ne'] using hm

def tests (lo b z : ℝ) : Fin 2 → RowRival → ℝ := ![test lo b,test lo z]

def event (R : Measure RowRival) (lo b z : ℝ) (N : ℕ) : Set (Fin N → RowRival) :=
  RivalGood.good R (tests lo b z) N (EntryModerateProfile.radius N)

lemma measurable_event (R : Measure RowRival) (lo b z : ℝ) (N : ℕ) :
    MeasurableSet (event R lo b z N) :=
  RivalGood.measurable_good R _ (by intro j; fin_cases j <;> exact test_measurable _ _) N _

lemma complement_le (R : Measure RowRival) [IsProbabilityMeasure R]
    {lo b z : ℝ} (hlo : 0 < lo) (hb : lo ≤ b) (hz : lo ≤ z) (N : ℕ) (hN : 0 < N) :
    (Measure.pi (fun _ : Fin N => R)).real (event R lo b z N)ᶜ ≤
      4*Real.exp (-2*Real.sqrt (N:ℝ)) := by
  have hh := RivalGood.good_complement_le R (tests lo b z)
    (by intro j; fin_cases j <;> exact (test_measurable _ _).aemeasurable)
    (by intro j; fin_cases j
        · exact ae_of_all _ (test_unit hlo hb)
        · exact ae_of_all _ (test_unit hlo hz)) N hN (radius_pos hN).le
  rw [show -2*(N:ℝ)*EntryModerateProfile.radius N^2=
    -2*((N:ℝ)*EntryModerateProfile.radius N^2) by ring,radius_exponent hN] at hh
  norm_num only [Fintype.card_fin,Nat.cast_ofNat] at hh
  exact hh

lemma event_test_error (R : Measure RowRival) {lo b z κ : ℝ} (hlo : 0 < lo)
    (N : ℕ) (r : Fin N → RowRival) (hr : r∈event R lo b z N) (j : Fin 2) :
    |empirical (rawReciprocal (![b,z] j)) N r-κ| ≤
      (EntryModerateProfile.radius N+|(∫ x,tests lo b z j x ∂ R)-lo*κ|)/lo := by
  have hh := abs_sub_le (RivalGood.empirical (tests lo b z) N r j)
    (∫ x,tests lo b z j x ∂ R) (lo*κ)
  have ht := hh.trans (add_le_add (hr j).le le_rfl)
  have he : RivalGood.empirical (tests lo b z) N r j=
      lo*empirical (rawReciprocal (![b,z] j)) N r := by
    have ht (y : RowRival) : tests lo b z j y=lo*rawReciprocal (![b,z] j) y := by
      fin_cases j <;> rfl
    change (∑ x,tests lo b z j (r x))/(N:ℝ)=
      lo*((∑ x,rawReciprocal (![b,z] j) (r x))/(N:ℝ))
    simp_rw [ht]
    rw [← Finset.mul_sum]
    ring
  rw [he,← mul_sub,abs_mul,abs_of_pos hlo] at ht
  exact (le_div_iff₀ hlo).mpr (by nlinarith)

def error (R : Measure RowRival) (lo b z a κ : ℝ) (N : ℕ) : ℝ :=
  (2*EntryModerateProfile.radius N+|(∫ x,test lo b x ∂ R)-lo*κ|+
      |(∫ x,test lo z x ∂ R)-lo*κ|)/lo+
    (2/lo)*(EntryModerateProfile.radius N/a+1/(N:ℝ))

lemma error_nonneg (R : Measure RowRival) {lo a : ℝ} (hlo : 0 < lo) (ha : 0 < a)
    (b z κ : ℝ) (N : ℕ) : 0 ≤ error R lo b z a κ N := by
  unfold error EntryModerateProfile.radius
  positivity

section OriginalMeans
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

theorem actual_test_mean_tendsto
    (i : Row) (V : Ω → ℝ) (B : ℕ → Ω → ℝ)
    (hV : Measurable V) (hB : ∀ m,Measurable (B m))
    (hvalue : μ.map V=LowChernoff.conditionalValueLaw i)
    (hadmissible : ∀ m,∀ᵐ ω ∂μ,B m ω ≤ V ω)
    (hactive : ∀ᵐ ω ∂μ,entry i < V ω → Tendsto (fun m => B m ω) atTop
      (𝓝 (ActiveGraphComponent.activeBid i (V ω))))
    {lo : ℝ} (hlo : 0 < lo)
    (b z u : ℕ → ℝ) (hbp : ∀ m,0 < b m) (hzlo : ∀ m,lo ≤ z m)
    (hz : Tendsto z atTop (𝓝 (entry i))) (hu : Tendsto u atTop (𝓝 0)) :
    Tendsto (fun m => ∫ r,test lo (z m) r ∂ rawTilt i (joint μ V (B m)) (b m) (u m))
      atTop (𝓝 (lo*reciprocalMean μ i V)) := by
  let G := fun m => joint μ V (B m)
  letI (m : ℕ) : IsProbabilityMeasure (G m) :=
    Measure.isProbabilityMeasure_map (hV.prodMk (hB m)).aemeasurable
  have hmean := (raw_reciprocal_population_tendsto μ i V B hV hB hvalue hadmissible hactive hlo z hzlo hz).const_mul lo
  have hm : Tendsto (fun m => ∫ r,test lo (z m) r ∂ RawMixedSource.source i (G m))
      atTop (𝓝 (lo*reciprocalMean μ i V)) := by
    simpa only [test,integral_const_mul] using hmean
  exact small_tilt_mean_tendsto (fun m => RawMixedSource.source i (G m))
    (fun m => RawMixedSource.demand (xi i) (b m)) (fun m => test lo (z m))
    (fun m => RawMixedSource.measurable_demand _ _) (fun m => test_measurable _ _)
    (fun m => ae_of_all _ (RawMixedSource.demand_bounds (xi_pos i) (hbp m)))
    (fun m => ae_of_all _ (test_unit hlo (hzlo m))) u hu hm

end OriginalMeans

lemma error_tendsto (R : ℕ → Measure RowRival) (lo a κ : ℝ)
    (b z : ℕ → ℝ) (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (hb : Tendsto (fun m => ∫ x,test lo (b m) x ∂ R m) atTop (𝓝 (lo*κ)))
    (hz : Tendsto (fun m => ∫ x,test lo (z m) x ∂ R m) atTop (𝓝 (lo*κ))) :
    Tendsto (fun m => error (R m) lo (b m) (z m) a κ (N m)) atTop (𝓝 0) := by
  have hr := radius_tendsto N hN
  have hi : Tendsto (fun m => 1/(N m:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp hN)
  have he1 := (hb.sub_const (lo*κ)).abs
  have he2 := (hz.sub_const (lo*κ)).abs
  simpa [error] using ((((hr.const_mul 2).add he1).add he2).div_const lo).add
    (((hr.div_const a).add hi).const_mul (2/lo))

end FCAppendix.Affine.Uniform06.EntryModerateReciprocal
