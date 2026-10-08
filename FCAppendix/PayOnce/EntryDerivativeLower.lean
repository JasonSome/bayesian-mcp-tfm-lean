import FCAppendix.PayOnce.DummyWeightedDerivative

namespace FCAppendix.PayOnce.EntryDerivativeLower
open MeasureTheory Set RareSuccessSlope

theorem entry_indicator_le_weightedSlope_add_bad {n : ℕ} (hn : 2 ≤ n)
    {p weight η κ a : ℝ} (hp : p ∈ Icc (0:ℝ) 1)
    (hw : weight ∈ Icc (0:ℝ) 1) (hη : η < 1) (hκ : 0 < κ) (ha : 0 < a)
    (hphi : ∀ q ∈ Icc (0:ℝ) η, a ≤ phi n q)
    {bad : Prop} [Decidable bad]
    (hgood : ¬bad → 0 < p → p ≤ η ∧ κ ≤ 1-weight) :
    (if 0 < p then a*κ else 0) ≤ weightedSlope n p weight+
      if bad then a*κ else 0 := by
  have hd := weightedSlope_nonneg hn hp (fun _ => hw.2)
  by_cases hb : bad
  · rw [if_pos hb]
    split_ifs <;> nlinarith
  · rw [if_neg hb,add_zero]
    by_cases hpos : 0 < p
    · rw [if_pos hpos]
      have hg := hgood hb hpos
      have hi : 0 < p ∧ p < 1 := ⟨hpos,hg.1.trans_lt hη⟩
      rw [weightedSlope,if_pos hi]
      exact mul_le_mul (hphi p ⟨hp.1,hg.1⟩) hg.2 hκ.le (phi_nonneg hn hp)
    · rw [if_neg hpos]
      exact hd

theorem integral_weightedSlope_ge_entry_sub_bad {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ} (hn : 2 ≤ n)
    {p weight : Ω → ℝ} (hp : Measurable p) (hw : Measurable weight)
    (hbound : ∀ ω, p ω ∈ Icc (0:ℝ) 1)
    (hweight : ∀ ω, weight ω ∈ Icc (0:ℝ) 1)
    {η κ a : ℝ} (hη : η < 1) (hκ : 0 < κ) (ha : 0 < a)
    (hphi : ∀ q ∈ Icc (0:ℝ) η, a ≤ phi n q)
    {E : Set Ω} (hE : MeasurableSet E)
    (hgood : ∀ᵐ ω ∂μ, ω ∉ E → 0 < p ω → p ω ≤ η ∧ κ ≤ 1-weight ω) :
    Integrable (fun ω => weightedSlope n (p ω) (weight ω)) μ ∧
      (a*κ)*(μ.real {ω | 0 < p ω}-μ.real E) ≤
        ∫ ω, weightedSlope n (p ω) (weight ω) ∂μ := by
  classical
  let A := {ω | 0 < p ω}
  have hA : MeasurableSet A := measurableSet_lt measurable_const hp
  have hI := integrable_weightedSlope μ hn hp hw hbound (fun ω _ => hweight ω)
  have hIA := (integrable_const (μ := μ) (a*κ)).indicator hA
  have hIE := (integrable_const (μ := μ) (a*κ)).indicator hE
  refine ⟨hI,?_⟩
  have hh := integral_mono_ae hIA (hI.add hIE) ?_
  · simp only [Pi.add_apply] at hh
    rw [integral_add hI hIE,integral_indicator hA,integral_indicator hE,
      setIntegral_const,setIntegral_const,smul_eq_mul,smul_eq_mul] at hh
    change μ.real {ω | 0 < p ω}*(a*κ) ≤
      (∫ ω, weightedSlope n (p ω) (weight ω) ∂μ)+μ.real E*(a*κ) at hh
    nlinarith
  · filter_upwards [hgood] with ω hω
    simpa only [A,indicator,mem_setOf_eq,Pi.add_apply] using
      entry_indicator_le_weightedSlope_add_bad hn (hbound ω) (hweight ω) hη hκ ha hphi hω

theorem absorb_bad_mass {D F E d b bhi : ℝ} (hd : 0 < d) (hb : 0 < b)
    (hbhi : b ≤ bhi) (hF : 0 ≤ F) (hbad : E ≤ F/2)
    (hderiv : (d/b)*(F-E) ≤ D) : (d/(2*bhi))*F ≤ D := by
  have hhalf : 0 ≤ F/2 := by positivity
  have hratio : d/bhi ≤ d/b := div_le_div_of_nonneg_left hd.le hb hbhi
  calc
    (d/(2*bhi))*F = (d/bhi)*(F/2) := by ring
    _ ≤ (d/b)*(F/2) := mul_le_mul_of_nonneg_right hratio hhalf
    _ ≤ (d/b)*(F-E) := mul_le_mul_of_nonneg_left (by linarith) (div_pos hd hb).le
    _ ≤ D := hderiv

noncomputable def entrySlopeConstant (n : ℕ) : ℝ :=
  (phi n 0/2)*(1/((n:ℝ)^3+1))

theorem entrySlopeConstant_pos {n : ℕ} (hn : 2 ≤ n) : 0 < entrySlopeConstant n := by
  unfold entrySlopeConstant
  exact mul_pos (half_pos (phi_zero_pos hn)) (by positivity)

end FCAppendix.PayOnce.EntryDerivativeLower

namespace FCAppendix.PayOnce.DummyKernel
open MeasureTheory Set RareSuccessSlope EntryDerivativeLower
variable {ι : Type*} [Fintype ι]

theorem coverage_deriv_ge_entry_sub_bad {n c : ℕ} (hn : 2 ≤ n)
    (μ : Measure (ι → ℝ)) [IsProbabilityMeasure μ]
    {b : ℝ} (hb : 0 < b) (hreg : ∀ᵐ r ∂μ, RegularClearing n c r b)
    {η a : ℝ} (hη : η < 1) (ha : 0 < a)
    (hphi : ∀ q ∈ Icc (0:ℝ) η, a ≤ phi n q)
    {E : Set (ι → ℝ)} (hE : MeasurableSet E)
    (hgood : ∀ᵐ r ∂μ, r ∉ E → allocation n c hn r b ≤ η) :
    HasDerivAt (coverage n c hn μ) (deriv (coverage n c hn μ) b) b ∧
      ((a*(1/((n:ℝ)^3+1)))/b)*
        (μ.real {r | 0 < allocation n c hn r b}-μ.real E) ≤
          deriv (coverage n c hn μ) b := by
  obtain ⟨weight,hw,hwb,hwgap,_,hd⟩ := exists_measurable_weight_coverage_derivative hn μ hb hreg
  have hi := integral_weightedSlope_ge_entry_sub_bad μ hn
    (measurable_allocation_fixed_bid hn b) hw (fun r => allocation_bounds hn r b) hwb
    hη (show 0 < 1/((n:ℝ)^3+1) by positivity) ha hphi hE (by
      filter_upwards [hgood] with r hr hnot _
      exact ⟨hr hnot,hwgap r⟩)
  refine ⟨hd.differentiableAt.hasDerivAt,?_⟩
  rw [hd.deriv]
  have hh := div_le_div_of_nonneg_right hi.2 hb.le
  simpa only [div_mul_eq_mul_div] using hh

theorem coverage_deriv_ge_entry_sub_tail {n c : ℕ} (hn : 2 ≤ n)
    (μ : Measure (ι → ℝ)) [IsProbabilityMeasure μ]
    {b : ℝ} (hb : 0 < b) (hreg : ∀ᵐ r ∂μ, RegularClearing n c r b)
    {η a : ℝ} (hη : η < 1) (ha : 0 < a)
    (hphi : ∀ q ∈ Icc (0:ℝ) η, a ≤ phi n q) :
    HasDerivAt (coverage n c hn μ) (deriv (coverage n c hn μ) b) b ∧
      ((a*(1/((n:ℝ)^3+1)))/b)*
        (μ.real {r | 0 < allocation n c hn r b}-μ.real {r | η ≤ allocation n c hn r b}) ≤
          deriv (coverage n c hn μ) b := by
  apply coverage_deriv_ge_entry_sub_bad hn μ hb hreg hη ha hphi
    (measurableSet_le measurable_const (measurable_allocation_fixed_bid hn b))
  exact Filter.Eventually.of_forall fun r hr => (lt_of_not_ge hr).le

theorem ae_coverage_deriv_ge_entry_sub_tail (G : Measure ℝ) [IsProbabilityMeasure G]
    (hatom : ∀ b : ℝ, 0 < b → G {b} = 0) {n c : ℕ} (hn : 2 ≤ n)
    {η a : ℝ} (hη : η < 1) (ha : 0 < a)
    (hphi : ∀ q ∈ Icc (0:ℝ) η, a ≤ phi n q) :
    ∀ᵐ b ∂G, 0 < b →
      HasDerivAt (coverage n c hn (Measure.pi (fun _ : ι => G)))
        (deriv (coverage n c hn (Measure.pi (fun _ : ι => G))) b) b ∧
      ((a*(1/((n:ℝ)^3+1)))/b)*
        ((Measure.pi (fun _ : ι => G)).real {r | 0 < allocation n c hn r b}-
          (Measure.pi (fun _ : ι => G)).real {r | η ≤ allocation n c hn r b}) ≤
        deriv (coverage n c hn (Measure.pi (fun _ : ι => G))) b := by
  filter_upwards [ae_regularClearing (ι := ι) (c := c) G hatom hn] with b hreg hb
  exact coverage_deriv_ge_entry_sub_tail hn _ hb (hreg hb) hη ha hphi

universe u

theorem exists_entry_deriv_cutoff {n : ℕ} (hn : 2 ≤ n) :
    ∃ η : ℝ, 0 < η ∧ η < 1 ∧ 0 < entrySlopeConstant n ∧
      ∀ {ι : Type u} [Fintype ι] (μ : Measure (ι → ℝ)) [IsProbabilityMeasure μ]
        (c : ℕ) (b : ℝ), 0 < b →
        (∀ᵐ r ∂μ, RegularClearing n c r b) →
        ∀ ε ∈ Ioc (0:ℝ) η,
          HasDerivAt (coverage n c hn μ) (deriv (coverage n c hn μ) b) b ∧
          (entrySlopeConstant n/b)*
            (μ.real {r | 0 < allocation n c hn r b}-μ.real {r | ε ≤ allocation n c hn r b}) ≤
              deriv (coverage n c hn μ) b := by
  obtain ⟨η,hη,hη1,hphi⟩ := phi_lower_near_zero hn
  refine ⟨η,hη,hη1,entrySlopeConstant_pos hn,?_⟩
  intro ι _ μ _ c b hb hreg ε hε
  exact coverage_deriv_ge_entry_sub_tail hn μ hb hreg (hε.2.trans_lt hη1)
    (half_pos (phi_zero_pos hn)) (fun q hq => hphi q ⟨hq.1,hq.2.trans hε.2⟩)

theorem coverage_deriv_ge_entry_of_tail_small {n c : ℕ} (hn : 2 ≤ n)
    (μ : Measure (ι → ℝ)) [IsProbabilityMeasure μ]
    {b bhi : ℝ} (hb : 0 < b) (hbhi : b ≤ bhi)
    (hreg : ∀ᵐ r ∂μ, RegularClearing n c r b)
    {η a : ℝ} (hη : η < 1) (ha : 0 < a)
    (hphi : ∀ q ∈ Icc (0:ℝ) η, a ≤ phi n q)
    (htail : μ.real {r | η ≤ allocation n c hn r b} ≤
      μ.real {r | 0 < allocation n c hn r b}/2) :
    HasDerivAt (coverage n c hn μ) (deriv (coverage n c hn μ) b) b ∧
      ((a*(1/((n:ℝ)^3+1)))/(2*bhi))*μ.real {r | 0 < allocation n c hn r b} ≤
        deriv (coverage n c hn μ) b := by
  have hh := coverage_deriv_ge_entry_sub_tail hn μ hb hreg hη ha hphi
  refine ⟨hh.1,?_⟩
  exact absorb_bad_mass (mul_pos ha (by positivity)) hb hbhi (measureReal_nonneg) htail hh.2

end FCAppendix.PayOnce.DummyKernel
