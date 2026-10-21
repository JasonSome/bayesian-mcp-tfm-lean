import FCAppendix.Affine.UniformFinite.ObservationTransport
import FCAppendix.Affine.UniformFinite.SourcePayoffContinuity

noncomputable section
set_option maxHeartbeats 1000000
namespace FCAppendix.Affine.UniformFinite
open Set MeasureTheory ProbabilityTheory
open Existence.Distributional

def numericCompactBid (i : Row) : NumericObservation i→ Bid i :=
  Sum.elim id (fun _=>⟨0,le_rfl,(Uniform05.cap_pos i).le⟩)

lemma numericCompactBid_coe (i : Row) (x : NumericObservation i) :
    (numericCompactBid i x:ℝ)=numericBid i x := by
  cases x <;> rfl

lemma measurable_numericCompactBid (i : Row) : Measurable (numericCompactBid i) :=
  measurable_id.sumElim measurable_const

lemma measurable_numericKind (i : Row) : Measurable (numericKind i) :=
  measurable_const.sumElim (measurable_of_countable _)

lemma measurable_numericBid (i : Row) : Measurable (numericBid i) :=
  measurable_subtype_coe.sumElim measurable_const

def numericFocalPayoff (i : Row) (N : ℕ) (G : Uniform05.RestrictedLaw i)
    (v : ℝ) (own : Bid i) (x : Fin N→ NumericObservation i) : ℝ :=
  rowPayoff i G (Source.countRowOfKind (Fin.cons 0 (fun j=> numericKind i (x j))))
    v (Fin.cons (own:ℝ) (fun j=> numericBid i (x j))) 0

theorem measurable_numericFocalPayoff (i : Row) (N : ℕ) (G : Uniform05.RestrictedLaw i)
    (v : ℝ) (own : Bid i) : Measurable (numericFocalPayoff i N G v own) := by
  let F : (Fin N→ Fin 3)×(Fin N→ Bid i)→ℝ := fun p=>
    rowPayoff i G (focalRow p.1) v
      (fun a : Fin (N+1)=>((Fin.cons own p.2 : Fin (N+1)→Bid i) a:ℝ)) 0
  have hF : Measurable F := by
    apply measurable_from_prod_countable_right
    intro kind
    have hb : Measurable (fun b : Fin N→ Bid i=> (Fin.cons own b : Fin (N+1)→Bid i)) := by
      apply measurable_pi_lambda
      intro a
      refine Fin.cases ?_ (fun j=>?_) a
      · exact measurable_const
      · exact measurable_pi_apply j
    have hmem : (0 : Fin (N+1))∈(focalRow kind).lower := by
      simp [focalRow,Source.countRowOfKind]
    have hs : Measurable (fun b : Fin N→Bid i =>
        SourceContinuity.fixedLawState i G (Fin.cons own b : Fin (N+1)→Bid i)) :=
      (SourceContinuity.measurable_fixedLawState i G).comp hb
    have hm : Measurable (fun b : Fin N→Bid i =>
        ((v:ℝ),SourceContinuity.fixedLawState i G (Fin.cons own b : Fin (N+1)→Bid i))) :=
      measurable_const.prodMk hs
    convert! (SourceContinuity.measurable_rowPayoff i (focalRow kind) 0 hmem).comp hm using 1
  have hk : Measurable (fun x : Fin N→ NumericObservation i=> fun j=> numericKind i (x j)) :=
    measurable_pi_lambda _ (fun j=>(measurable_numericKind i).comp (measurable_pi_apply j))
  have hb : Measurable (fun x : Fin N→ NumericObservation i=> fun j=> numericCompactBid i (x j)) :=
    measurable_pi_lambda _ (fun j=>(measurable_numericCompactBid i).comp (measurable_pi_apply j))
  convert! hF.comp (hk.prodMk hb) using 1
  funext x
  change rowPayoff i G _ v _ 0=rowPayoff i G _ v _ 0
  congr 2
  funext a
  refine Fin.cases ?_ (fun j=>?_) a
  · rfl
  · simpa only [Fin.cons_succ] using (numericCompactBid_coe i (x j)).symm

lemma numericFocalPayoff_bound (i : Row) (N : ℕ) (G : Uniform05.RestrictedLaw i)
    (v : ℝ) (own : Bid i) (x : Fin N→ NumericObservation i) :
    |numericFocalPayoff i N G v own x|≤|v|+(1+|Uniform05.eta i|)*|(own:ℝ)| := by
  simpa [numericFocalPayoff] using rowPayoff_bound i G
    (Source.countRowOfKind (Fin.cons 0 (fun j=> numericKind i (x j))))
    v (Fin.cons (own:ℝ) (fun j=> numericBid i (x j))) 0

@[simp] lemma numericFocalPayoff_encode (i : Row) (N : ℕ)
    (G : Uniform05.RestrictedLaw i) (v : ℝ) (own : Bid i)
    (kind : Fin N→ Fin 3) (b : Fin N→ Bid i) :
    numericFocalPayoff i N G v own (encodeCategoryRow i N (kind,b))=
      rowPayoff i G (focalRow kind) v (focalBids i kind own b) 0 := by
  simp [numericFocalPayoff,encodeCategoryRow,focalRow,focalBids]

theorem rawUtility_eq_original_observation_integral (i : Row) (N : ℕ)
    (G : Uniform05.RestrictedLaw i) (v : ℝ) (own : Bid i) :
    rawUtility i N G v own=
      ∫x,numericFocalPayoff i N G v own (fun j=> dropValue i (x j))
        ∂Measure.pi (fun _ : Fin N=> Source.observationLaw i G) := by
  rw [integral_original_observation_row i G N (numericFocalPayoff i N G v own)
    (measurable_numericFocalPayoff i N G v own) _
    (numericFocalPayoff_bound i N G v own)]
  simp only [numericFocalPayoff_encode,rawUtility]

end FCAppendix.Affine.UniformFinite
