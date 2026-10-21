import FCAppendix.Affine.Hybrid.Tail03.EarlySourceAdapter
import FCAppendix.Affine.Hybrid.Tail03.Pareto

noncomputable section
namespace FCAppendix.Affine.Hybrid.Tail03.OriginalLawIdentity
open MeasureTheory ProbabilityTheory Set

lemma band_density_eq (l u v : ℝ) :
    Tail04.bandDensity l u v=bandPDF l u v := by
  by_cases hv : v∈Icc l u <;> simp [Tail04.bandDensity,bandPDF,hv]

lemma pareto_density_eq (M v : ℝ) (hM : 0<M) :
    Tail04.paretoDensity M v=paretoPDFReal M 10 v := by
  by_cases hv : M≤v
  · have hv0 : 0<v:=hM.trans_le hv
    unfold Tail04.paretoDensity
    rw [Set.indicator_of_mem (show v∈Ici M from hv)]
    simp only [paretoPDFReal,if_pos hv,Tail04.powerTail]
    rw [show (-(10+1):ℝ)=-(11:ℝ) by norm_num,
      Real.rpow_neg (div_nonneg hv0.le hM.le),Real.rpow_neg hv0.le,
      show M^(10:ℝ)=M^10 from Real.rpow_natCast M 10,
      show (v/M)^(11:ℝ)=(v/M)^11 from Real.rpow_natCast (v/M) 11,
      show v^(11:ℝ)=v^11 from Real.rpow_natCast v 11]
    field_simp [hM.ne',hv0.ne']
  · simp [Tail04.paretoDensity,paretoPDFReal,hv]

lemma density_eq {eta1 eta2 : ℝ} (p : Parameters eta1 eta2) (v : ℝ) :
    Tail04.valueDensity (EarlySourceAdapter.values p) v=mixturePDF p.lawInput v := by
  unfold Tail04.valueDensity mixturePDF
  simp only [EarlySourceAdapter.values,Parameters.lawInput,
    band_density_eq,
    Tail04.lowMass,Tail04.partialMass,Tail04.activeMass,Tail04.delta,
    lowMass,partialMass,activeMass,delta]
  rw [pareto_density_eq p.tailFloor v (show 0<p.tailFloor from p.lawInput.M_pos)]
  ring

lemma valueLaw_eq_commonLaw {eta1 eta2 : ℝ} (p : Parameters eta1 eta2) :
    Tail04.valueLaw (EarlySourceAdapter.values p)=(commonLaw p : Measure ℝ) := by
  change Tail04.valueLaw (EarlySourceAdapter.values p)=mixtureMeasure p.lawInput
  rw [mixture_eq_withDensity]
  unfold Tail04.valueLaw
  congr 1
  funext v
  rw [density_eq]

lemma capacity_eq (m : ℕ) : Tail04.marketCapacity m=sourceCapacity m := rfl

end FCAppendix.Affine.Hybrid.Tail03.OriginalLawIdentity
