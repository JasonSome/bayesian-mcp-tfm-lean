import FCAppendix.Affine.UniformFinite.FiniteExperiment
import FCAppendix.Affine.UniformFinite.ObservationConcentration
import FCAppendix.Affine.LowBody.NoisyExpectedLoss

noncomputable section
namespace FCAppendix.Affine.UniformFinite
open MeasureTheory ProbabilityTheory Set
open Existence.Distributional
open scoped BigOperators

abbrev NumericObservation (i : Row) := Bid i ⊕ Fin 2

def dropValue (i : Row) : Source.Observation i→ NumericObservation i :=
  Sum.elim (fun p=> Sum.inl p.2) Sum.inr

lemma measurable_dropValue (i : Row) : Measurable (dropValue i) :=
  (measurable_inl.comp measurable_snd).sumElim measurable_inr

def numericObservationLaw (i : Row) (G : Uniform05.RestrictedLaw i) :
    Measure (NumericObservation i) :=
  ENNReal.ofReal (Uniform05.t i) • (G.bidLaw : Measure (Bid i)).map Sum.inl+
    ENNReal.ofReal ((1-Uniform05.t i)/2) • Measure.dirac (Sum.inr 0)+
    ENNReal.ofReal ((1-Uniform05.t i)/2) • Measure.dirac (Sum.inr 1)

lemma dropValue_law (i : Row) (G : Uniform05.RestrictedLaw i) :
    (Source.observationLaw i G).map (dropValue i)=numericObservationLaw i G := by
  have hm := measurable_dropValue i
  rw [Source.observationLaw,Measure.map_add _ _ hm,Measure.map_add _ _ hm,
    Measure.map_smul,Measure.map_smul,Measure.map_smul,
    Measure.map_dirac' hm,Measure.map_dirac' hm]
  unfold Source.lowerObservationLaw
  rw [Measure.map_map hm measurable_inl]
  have he : (G.1 : Measure (ℝ×Bid i)).map
      (fun p=> Sum.inl p.2 : (ℝ×Bid i)→ NumericObservation i)=
      (G.bidLaw : Measure (Bid i)).map Sum.inl := by
    rw [Uniform05.RestrictedLaw.bidLaw_coe,Measure.map_map measurable_inl measurable_snd]
    rfl
  simp only [dropValue,Function.comp_def,Sum.elim_inl,Sum.elim_inr,
    he,numericObservationLaw]

instance numericObservationLaw_probability (i : Row) (G : Uniform05.RestrictedLaw i) :
    IsProbabilityMeasure (numericObservationLaw i G) := by
  rw [← dropValue_law i G]
  exact Measure.isProbabilityMeasure_map (measurable_dropValue i).aemeasurable

def encodeCategory (i : Row) (p : Fin 3×Bid i) : NumericObservation i :=
  if p.1=0 then Sum.inl p.2 else if p.1=1 then Sum.inr 0 else Sum.inr 1

lemma measurable_encodeCategory (i : Row) : Measurable (encodeCategory i) :=
  Measurable.ite (measurableSet_eq_fun measurable_fst measurable_const)
    (measurable_inl.comp measurable_snd)
    (Measurable.ite (measurableSet_eq_fun measurable_fst measurable_const)
      measurable_const measurable_const)

lemma category_measure_explicit (i : Row) :
    FiniteLaw.probabilityMeasure (categoryLaw i)=
      ENNReal.ofReal (Uniform05.t i) • Measure.dirac 0+
      ENNReal.ofReal ((1-Uniform05.t i)/2) • Measure.dirac 1+
      ENNReal.ofReal ((1-Uniform05.t i)/2) • Measure.dirac 2 := by
  unfold FiniteLaw.probabilityMeasure
  simp [categoryLaw,Fin.sum_univ_succ, add_assoc]

lemma encodeCategory_dirac_prod (i : Row) (mu : Measure (Bid i)) [SFinite mu]
    (k : Fin 3) :
    ((Measure.dirac k).prod mu).map (encodeCategory i)=
      mu.map (fun b=> encodeCategory i (k,b)) := by
  rw [Measure.dirac_prod]
  have h := Measure.map_map (measurable_encodeCategory i)
    ((measurable_const (a := k)).prodMk measurable_id) (μ := mu)
  simpa only [Function.comp_def, id_eq] using h

theorem encodeCategory_law (i : Row) (G : Uniform05.RestrictedLaw i) :
    ((FiniteLaw.probabilityMeasure (categoryLaw i)).prod
      (G.bidLaw : Measure (Bid i))).map (encodeCategory i)=numericObservationLaw i G := by
  rw [category_measure_explicit,Measure.add_prod,Measure.add_prod,
    Measure.prod_smul_left,Measure.prod_smul_left,Measure.prod_smul_left,
    Measure.map_add _ _ (measurable_encodeCategory i),
    Measure.map_add _ _ (measurable_encodeCategory i),
    Measure.map_smul,Measure.map_smul,Measure.map_smul,
    encodeCategory_dirac_prod,encodeCategory_dirac_prod,encodeCategory_dirac_prod]
  simp only [encodeCategory,ite_true,show (1:Fin 3)≠0 by decide,
    show (2:Fin 3)≠0 by decide,show (2:Fin 3)≠1 by decide,if_false,
    Measure.map_const,measure_univ,one_smul,numericObservationLaw]

def encodeCategoryRow (i : Row) (N : ℕ)
    (p : (Fin N→ Fin 3)×(Fin N→ Bid i)) : Fin N→ NumericObservation i :=
  fun j=> encodeCategory i (p.1 j,p.2 j)

lemma measurable_encodeCategoryRow (i : Row) (N : ℕ) :
    Measurable (encodeCategoryRow i N) :=
  measurable_pi_lambda _ (fun j=>(measurable_encodeCategory i).comp
    (((measurable_pi_apply j).comp measurable_fst).prodMk
      ((measurable_pi_apply j).comp measurable_snd)))

theorem encodeCategoryRow_law (i : Row) (G : Uniform05.RestrictedLaw i) (N : ℕ) :
    ((FiniteLaw.probabilityMeasure (categoryRowLaw i N)).prod
      (rowLaw N G.bidLaw : Measure (Fin N→ Bid i))).map (encodeCategoryRow i N)=
      Measure.pi (fun _ : Fin N=> numericObservationLaw i G) := by
  rw [categoryRowLaw,LowBody.probabilityMeasure_iid,rowLaw_eq_pi]
  let e := MeasurableEquiv.arrowProdEquivProdArrow (Fin 3) (Bid i) (Fin N)
  have hp := (measurePreserving_arrowProdEquivProdArrow (Fin 3) (Bid i) (Fin N)
    (fun _=> FiniteLaw.probabilityMeasure (categoryLaw i))
    (fun _=>(G.bidLaw : Measure (Bid i)))).symm
  have hm : Measurable (fun p : Fin N→ Fin 3×Bid i=> fun j=> encodeCategory i (p j)) :=
    measurable_pi_lambda _ (fun j=>(measurable_encodeCategory i).comp (measurable_pi_apply j))
  calc
    _ = (((Measure.pi (fun _ : Fin N=> FiniteLaw.probabilityMeasure (categoryLaw i))).prod
        (Measure.pi (fun _ : Fin N=>(G.bidLaw : Measure (Bid i))))).map e.symm).map
          (fun p : Fin N→ Fin 3×Bid i=> fun j=> encodeCategory i (p j)) := by
      rw [Measure.map_map hm hp.measurable]
      rfl
    _ = _ := by
      rw [hp.map_eq,Measure.pi_map_pi (fun _=>(measurable_encodeCategory i).aemeasurable),
        encodeCategory_law]

theorem dropValueRow_law (i : Row) (G : Uniform05.RestrictedLaw i) (N : ℕ) :
    (Measure.pi (fun _ : Fin N=> Source.observationLaw i G)).map
      (fun x=> fun j=> dropValue i (x j))=
      Measure.pi (fun _ : Fin N=> numericObservationLaw i G) := by
  rw [Measure.pi_map_pi (fun _=>(measurable_dropValue i).aemeasurable)]
  simp only [dropValue_law]

theorem integral_original_observation_row (i : Row) (G : Uniform05.RestrictedLaw i)
    (N : ℕ) (f : (Fin N→ NumericObservation i)→ℝ) (hf : Measurable f)
    (C : ℝ) (hC : ∀x,|f x|≤ C) :
    (∫x,f (fun j=> dropValue i (x j))
      ∂Measure.pi (fun _ : Fin N=> Source.observationLaw i G))=
      (categoryRowLaw i N).expect (fun kind=>
        ∫b : Fin N→ Bid i,f (encodeCategoryRow i N (kind,b))
          ∂(rowLaw N G.bidLaw : Measure (Fin N→ Bid i))) := by
  have hdrop : Measurable (fun x : Fin N→ Source.Observation i=> fun j=> dropValue i (x j)) :=
    measurable_pi_lambda _ (fun j=>(measurable_dropValue i).comp (measurable_pi_apply j))
  have henc := measurable_encodeCategoryRow i N
  have hi : Integrable (fun p=> f (encodeCategoryRow i N p))
      ((FiniteLaw.probabilityMeasure (categoryRowLaw i N)).prod
        (rowLaw N G.bidLaw : Measure (Fin N→ Bid i))) :=
    Integrable.of_bound (hf.comp henc).aestronglyMeasurable C
      (ae_of_all _ (fun p=> by simpa only [Real.norm_eq_abs] using hC (encodeCategoryRow i N p)))
  rw [← integral_map hdrop.aemeasurable hf.aestronglyMeasurable,
    dropValueRow_law,← encodeCategoryRow_law,
    integral_map henc.aemeasurable hf.aestronglyMeasurable,
    integral_prod _ hi,LowBody.integral_probabilityMeasure]

def numericKind (i : Row) : NumericObservation i→ Fin 3 :=
  Sum.elim (fun _=>0) (fun j=> if j=0 then 1 else 2)

def numericBid (i : Row) : NumericObservation i→ℝ :=
  Sum.elim (fun b=>(b:ℝ)) (fun _=>0)

@[simp] theorem numericKind_encodeCategory (i : Row) (k : Fin 3) (b : Bid i) :
    numericKind i (encodeCategory i (k,b))=k := by
  fin_cases k <;> simp [numericKind,encodeCategory]

@[simp] theorem numericBid_encodeCategory (i : Row) (k : Fin 3) (b : Bid i) :
    numericBid i (encodeCategory i (k,b))=(if k=0 then (b:ℝ) else 0) := by
  fin_cases k <;> simp [numericBid,encodeCategory]

theorem numericFocal_row (i : Row) {N : ℕ} (kind : Fin N→ Fin 3) (b : Fin N→ Bid i)
    (own : ℝ) :
    Source.countRowOfKind (Fin.cons 0 (fun j=> numericKind i (encodeCategoryRow i N (kind,b) j)))=
      focalRow kind ∧
    Fin.cons own (fun j=> numericBid i (encodeCategoryRow i N (kind,b) j))=
      focalBids i kind own b := by
  constructor
  · simp [encodeCategoryRow,focalRow]
  · simp [encodeCategoryRow,focalBids]

end FCAppendix.Affine.UniformFinite
