import FCAppendix.Affine.Hybrid.Tail03.Law

noncomputable section
namespace FCAppendix.Affine.Hybrid.Tail03
open MeasureTheory ProbabilityTheory Set

theorem commonLaw_supported_on_four_bands (p : LawInput) :
    ∀ᵐ v ∂(mixFourComponents p : Measure ℝ),
      (0≤ v ∧ v≤ p.d0) ∨
      (2-p.w≤ v ∧ v≤2+p.w) ∨
      (p.vA-p.w≤ v ∧ v≤ p.vA+p.w) ∨ p.M≤ v := by
  change ∀ᵐ v ∂mixtureMeasure p, _
  unfold mixtureMeasure
  apply ae_add_measure_iff.mpr
  refine ⟨ae_add_measure_iff.mpr ⟨ae_add_measure_iff.mpr ⟨?_,?_⟩,?_⟩,?_⟩
  · exact Measure.ae_smul_measure
      ((bandMeasure_supported 0 p.d0).mono fun _ hv => Or.inl hv) _
  · exact Measure.ae_smul_measure
      ((bandMeasure_supported (2-p.w) (2+p.w)).mono fun _ hv => Or.inr (Or.inl hv)) _
  · exact Measure.ae_smul_measure
      ((bandMeasure_supported (p.vA-p.w) (p.vA+p.w)).mono fun _ hv =>
        Or.inr (Or.inr (Or.inl hv))) _
  · exact Measure.ae_smul_measure
      ((pareto_supported p.M).mono fun _ hv => Or.inr (Or.inr (Or.inr hv))) _

theorem commonLaw_gap_mass_zero (p : LawInput) :
    (mixFourComponents p : Measure ℝ) (Ioo p.d0 (2-p.w))=0 ∧
    (mixFourComponents p : Measure ℝ) (Ioo (2+p.w) (p.vA-p.w))=0 ∧
    (mixFourComponents p : Measure ℝ) (Ioo (p.vA+p.w) p.M)=0 := by
  have hs := commonLaw_supported_on_four_bands p
  refine ⟨?_,?_,?_⟩
  all_goals
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hs] with v hv
    intro hgap
    rcases hgap with ⟨hg0,hg1⟩
    rcases hv with ⟨hv0,hv1⟩ | ⟨hv0,hv1⟩ | ⟨hv0,hv1⟩ | hv0
    all_goals linarith [p.w_pos,p.low_partial,p.partial_bulk,p.bulk_tail]

end FCAppendix.Affine.Hybrid.Tail03
