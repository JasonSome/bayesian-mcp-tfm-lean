import FCAppendix.Existence.R01PayOnceClippingLimit

noncomputable section
namespace FCAppendix.Existence.PayOnceBounded
open Set Filter Topology MeasureTheory ProbabilityTheory
open FCAppendix.Existence.Distributional

theorem tendsto_expected_profilePayoff {W : ℝ} (hW : 0<W)
    (m n c : ℕ) (hn : 2≤n) (i : Fin m)
    (π : ℕ→ProbabilityMeasure (Value W × FloorAction 0 W))
    (π₀ : ProbabilityMeasure (Value W × FloorAction 0 W))
    (hπ : Tendsto π atTop (𝓝 π₀))
    (hzero : (π₀ : Measure (Value W × FloorAction 0 W))
      {z|present z.2=true ∧ bid z.2=0}=0) :
    Tendsto (fun j=>∫x,positiveProfilePayoff m n c x i
      ∂(rowLaw m (π j) : Measure (Fin m→Value W × FloorAction 0 W))) atTop
      (𝓝 (∫x,positiveProfilePayoff m n c x i
        ∂(rowLaw m π₀ : Measure (Fin m→Value W × FloorAction 0 W)))) := by
  letI : OpensMeasurableSpace (Fin m→Value W × FloorAction 0 W) := inferInstance
  let P := fun ν : ProbabilityMeasure (Value W × FloorAction 0 W)=>
    ∫x,positiveProfilePayoff m n c x i ∂(rowLaw m ν : Measure (Fin m→Value W × FloorAction 0 W))
  let K : ℝ := (2*W)*m
  have hK : 0≤K := by dsimp [K]; positivity
  let δ : ℕ→ℝ := fun k=>W/(k+1)
  have hδ : ∀k,0<δ k := by intro k; dsimp [δ]; positivity
  have hδW : ∀k,δ k≤W := by
    intro k
    apply (div_le_iff₀ (by positivity : (0:ℝ)<k+1)).mpr
    nlinarith [show (0:ℝ)≤k from Nat.cast_nonneg k]
  have hδ0 : Tendsto δ atTop (𝓝 0) := by
    convert (tendsto_const_nhds.mul (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ))) using 1
    · funext k; dsimp [δ]; ring
    · simp
  have hmass := smallActive_mass_tendsto_zero π₀ hzero δ hδ0
  apply Metric.tendsto_nhds.mpr
  intro e he
  let r : ℝ := e/(6*(K+1))
  have hr : 0<r := by dsimp [r]; positivity
  have hKr : K*r<e/3 := by
    have hden : 0<6*(K+1) := by positivity
    have heq : r*(6*(K+1))=e := by dsimp [r]; field_simp
    nlinarith
  obtain ⟨k,hk⟩ := (hmass.eventually (Iio_mem_nhds hr)).exists
  let C := fun ν : ProbabilityMeasure (Value W × FloorAction 0 W)=>
    ∫x,clippedProfilePayoff m n c (δ k) (hδW k) x i
      ∂(rowLaw m ν : Measure (Fin m→Value W × FloorAction 0 W))
  have hc : Continuous C :=
    (ProbabilityMeasure.continuous_integral_continuousMap
      (⟨_,continuous_clippedProfilePayoff m n c hn (δ k) (hδ k) (hδW k) i⟩ :
        C(Fin m→Value W × FloorAction 0 W,ℝ))).comp (continuous_rowLaw m)
  have hC : ∀ᶠj in atTop,|C (π j)-C π₀|<e/3 := by
    have ht := hc.continuousAt.tendsto.comp hπ
    simpa only [Real.dist_eq,Function.comp_apply] using
      (Metric.tendsto_nhds.mp ht (e/3) (by linarith))
  have hM := eventually_closed_mass_lt π π₀ hπ (smallActive (δ k))
    (isClosed_smallActive (δ k)) r hk
  have h0 : |C π₀-P π₀|≤K*(π₀ : Measure (Value W × FloorAction 0 W)).real (smallActive (δ k)) :=
    abs_expected_profile_clipping_error m n c hn (δ k) (hδ k) (hδW k) π₀ i
  have h0r : |C π₀-P π₀|<e/3 := (h0.trans
    (mul_le_mul_of_nonneg_left hk.le hK)).trans_lt hKr
  filter_upwards [hC,hM] with j hjC hjM
  have hj : |C (π j)-P (π j)|≤K*(π j : Measure (Value W × FloorAction 0 W)).real (smallActive (δ k)) :=
    abs_expected_profile_clipping_error m n c hn (δ k) (hδ k) (hδW k) (π j) i
  have hjr : |P (π j)-C (π j)|<e/3 := by
    rw [abs_sub_comm]
    exact (hj.trans (mul_le_mul_of_nonneg_left hjM.le hK)).trans_lt hKr
  have htri := abs_sub_le (P (π j)) (C (π j)) (P π₀)
  have htri' := abs_sub_le (C (π j)) (C π₀) (P π₀)
  change |P (π j)-P π₀|<e
  linarith

end FCAppendix.Existence.PayOnceBounded
