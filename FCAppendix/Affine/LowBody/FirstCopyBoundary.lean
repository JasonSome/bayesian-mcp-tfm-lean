import FCAppendix.Affine.LowBody.BoundaryParameters
import FCAppendix.Affine.LowBody.HarmfulJumpBound

noncomputable section
namespace FCAppendix.Affine.LowBody
open MeasureTheory ProbabilityTheory Set Classical Filter Topology
open scoped BigOperators ENNReal

def higherAtSet (b : ℝ) : Set RowRival :=
  {x | x.1=1 ∨ x.1=2 ∨ (x.1=0 ∧ b<x.2)}

theorem measurableSet_higherAtSet (b : ℝ) : MeasurableSet (higherAtSet b) :=
  (measurableSet_eq_fun measurable_fst measurable_const).union
    ((measurableSet_eq_fun measurable_fst measurable_const).union
      ((measurableSet_eq_fun measurable_fst measurable_const).inter
        (measurableSet_lt measurable_const measurable_snd)))

section Law
variable (s a h : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ a) (hh : 0 ≤ h) (hsum : s+a+h=1)
    (G : Measure ℝ) [IsProbabilityMeasure G]
local notation "mu"=>rivalLaw s a h G
include hs ha hh hsum

omit hsum in
theorem higherAtSet_probability (b : ℝ) :
    (mu).real (higherAtSet b)=higherBidProbability s a h G b := by
  have hlow : Measurable (fun x : ℝ=>((0:Fin 4),x)):=measurable_const.prodMk measurable_id
  have hp : (fun x : ℝ=>((0:Fin 4),x)) ⁻¹' higherAtSet b=Ioi b := by
    ext x
    change ((0:Fin 4)=1 ∨ (0:Fin 4)=2 ∨ ((0:Fin 4)=0 ∧ b<x))↔b<x
    norm_num [Fin.ext_iff]
  have h1 : ((1:Fin 4),0)∈higherAtSet b:=Or.inl rfl
  have h2 : ((2:Fin 4),0)∈higherAtSet b:=Or.inr (Or.inl rfl)
  have h3 : ((3:Fin 4),0)∉higherAtSet b:=by
    change ¬((3:Fin 4)=1 ∨ (3:Fin 4)=2 ∨ ((3:Fin 4)=0 ∧ b<0))
    norm_num [Fin.ext_iff]
  have he : mu (higherAtSet b)=ENNReal.ofReal s*G (Ioi b)+ENNReal.ofReal a+ENNReal.ofReal (h/2) := by
    simp only [rivalLaw,Measure.add_apply,Measure.smul_apply,smul_eq_mul]
    rw [Measure.map_apply hlow (measurableSet_higherAtSet b),hp]
    simp only [Measure.dirac_apply,Set.indicator_of_mem h1,Set.indicator_of_mem h2,
      Set.indicator_of_notMem h3,Pi.one_apply,mul_one,mul_zero,add_zero]
  rw [measureReal_def,he]
  have hsG : ENNReal.ofReal s*G (Ioi b)≠⊤:=ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top G _)
  rw [ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨hsG,ENNReal.ofReal_ne_top⟩) ENNReal.ofReal_ne_top,
    ENNReal.toReal_add hsG ENNReal.ofReal_ne_top,ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hs,ENNReal.toReal_ofReal ha,
    ENNReal.toReal_ofReal (by positivity : 0≤h/2)]
  change s*G.real (Ioi b)+a+h/2=a+h/2+s*G.real (Ioi b)
  ring

theorem actual_higher_boundary_probability (N K : ℕ) (b : ℝ) :
    (Measure.pi (fun _ : Fin N=>mu)).real
      {ω | PiBinomial.count (higherAtSet b) Finset.univ ω=K}=
      PiBinomial.pmf N (higherBidProbability s a h G b) K := by
  letI : IsProbabilityMeasure mu:=rivalLaw_isProbability s a h hs ha hh hsum G
  have hcountlaw:=PiBinomial.measureReal_count_eq mu (higherAtSet b) (measurableSet_higherAtSet b)
    (Finset.univ : Finset (Fin N)) K
  simpa only [Finset.card_univ,Fintype.card_fin,higherAtSet_probability s a h hs ha hh G] using hcountlaw

def firstCopyBoundary {N : ℕ} (c : ℕ) (b : ℝ) : Set (Fin N→RowRival) :=
  {ω | PiBinomial.count (higherAtSet b) Finset.univ ω=c-1} \ rowBothUnderflow c

omit hs ha hh hsum in
theorem measurableSet_firstCopyBoundary {N : ℕ} (c : ℕ) (b : ℝ) :
    MeasurableSet (firstCopyBoundary (N:=N) c b) :=
  (measurableSet_eq_fun (PiBinomial.measurable_count (higherAtSet b) (measurableSet_higherAtSet b)
    Finset.univ) measurable_const).diff (measurableSet_rowBothUnderflow c)

theorem firstCopyBoundary_probability_lower (N c : ℕ) (b : ℝ) :
    PiBinomial.pmf N (higherBidProbability s a h G b) (c-1)-
      (CommonList.iid (categoryLaw s a h hs ha hh hsum G) N).prob (BothUnderflow c)≤
      (Measure.pi (fun _ : Fin N=>mu)).real (firstCopyBoundary c b) := by
  letI : IsProbabilityMeasure mu:=rivalLaw_isProbability s a h hs ha hh hsum G
  let P:=Measure.pi (fun _ : Fin N=>mu)
  let E : Set (Fin N→RowRival):={ω | PiBinomial.count (higherAtSet b) Finset.univ ω=c-1}
  have hd:=measureReal_inter_add_sdiff (μ:=P) (s:=E) (measurableSet_rowBothUnderflow c)
  have hm : P.real (E∩rowBothUnderflow c)≤P.real (rowBothUnderflow c):=
    measureReal_mono inter_subset_right
  rw [show P.real E=PiBinomial.pmf N (higherBidProbability s a h G b) (c-1) from
      actual_higher_boundary_probability s a h hs ha hh hsum G N (c-1) b] at hd
  have hu : P.real (rowBothUnderflow c)=
      (CommonList.iid (categoryLaw s a h hs ha hh hsum G) N).prob (BothUnderflow c):=
    rowBothUnderflow_probability s a h hs ha hh hsum G N c
  rw [hu] at hm
  change _≤P.real (E\rowBothUnderflow c)
  linarith

end Law

theorem eventually_firstCopyBoundary_uniform (s a h : ℝ)
    (hs : 0 ≤ s) (ha : 0 ≤ a) (hh : 0 ≤ h) (hsum : s+a+h=1)
    (c : ℕ→ℕ) (ρ : ℝ) (hρ : 0<ρ) (hrank : ρ<a+h/2) (hhpos : 0<h)
    (hc : Filter.Tendsto (fun m=>(c m:ℝ)/(m:ℝ)) Filter.atTop (𝓝 ρ)) :
    ∀ᶠm : ℕ in Filter.atTop,∀(G : Measure ℝ)(hG : IsProbabilityMeasure G)(b : ℝ),
      boundary c (1-h/2) m-
        jointUnderflow (@categoryLaw s a h hs ha hh hsum G hG) c 2 m≤
        (Measure.pi (fun _ : Fin (m-2)=>rivalLaw s a h G)).real
          (firstCopyBoundary (c m) b) := by
  have hqq : a+h/2≤1-h/2:=by linarith
  have hq1 : 1-h/2<1:=by linarith
  have he:=eventually_boundary_uniform c ρ (a+h/2) (1-h/2) hρ hrank hqq hq1 hc
  filter_upwards [he] with m hm G hG b
  letI:=hG
  have hparam:=higherBidProbability_bounds s a h hs hsum G b
  have hlo:=hm _ hparam
  have hactual:=firstCopyBoundary_probability_lower s a h hs ha hh hsum G (m-2) (c m) b
  exact (sub_le_sub_right hlo _).trans hactual

end FCAppendix.Affine.LowBody
