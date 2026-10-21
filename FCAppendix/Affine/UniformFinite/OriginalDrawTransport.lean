import FCAppendix.Affine.UniformFinite.ActualSurplus
import FCAppendix.Affine.UniformFinite.ObservationTransport

noncomputable section
namespace FCAppendix.Affine.UniformFinite
open MeasureTheory ProbabilityTheory Set
open Existence.Distributional
open scoped BigOperators

abbrev LowerDraw (i : Row) := (Value i × unitInterval) × unitInterval
abbrev RivalDraw (i : Row) := Fin 3 × LowerDraw i

def lowerDrawLaw (i : Row) (pi : Joint i) : Measure (LowerDraw i) :=
  (pi.1 : Measure (Value i × unitInterval)).prod volume

instance lowerDrawLaw_probability (i : Row) (pi : Joint i) :
    IsProbabilityMeasure (lowerDrawLaw i pi) := inferInstanceAs
      (IsProbabilityMeasure ((pi.1 : Measure (Value i × unitInterval)).prod
        (volume : Measure unitInterval)))

def rivalDrawLaw (i : Row) (pi : Joint i) : Measure (RivalDraw i) :=
  (FiniteLaw.probabilityMeasure (categoryLaw i)).prod (lowerDrawLaw i pi)

instance rivalDrawLaw_probability (i : Row) (pi : Joint i) :
    IsProbabilityMeasure (rivalDrawLaw i pi) := inferInstanceAs
      (IsProbabilityMeasure ((FiniteLaw.probabilityMeasure (categoryLaw i)).prod
        (lowerDrawLaw i pi)))

def drawBid (i : Row) (eps : unitInterval) (x : LowerDraw i) : Bid i :=
  noisyBid i (eps,x)

lemma measurable_drawBid (i : Row) (eps : unitInterval) :
    Measurable (drawBid i eps) :=
  ((continuous_noisyBid i).comp (continuous_const.prodMk continuous_id)).measurable

theorem lowerDraw_bid_law (i : Row) (eps : unitInterval) (pi : Joint i) :
    (lowerDrawLaw i pi).map (drawBid i eps)=
      ((restrictedLaw i (eps,pi)).bidLaw : Measure (Bid i)) := by
  rw [restrictedLaw_bidLaw]
  change _=(((pi.1 : Measure (Value i × unitInterval)).prod volume).map
    (fun x : LowerDraw i => (x.1.1,noisyBid i (eps,x)))).map Prod.snd
  rw [Measure.map_map measurable_snd
    (show Measurable (fun x : LowerDraw i => (x.1.1,noisyBid i (eps,x))) from
      (measurable_fst.comp measurable_fst).prodMk (measurable_drawBid i eps))]
  rfl

theorem lowerDraw_value_law (i : Row) (pi : Joint i) :
    (lowerDrawLaw i pi).map (fun x => x.1.1)=lowerMeasure i := by
  change (((pi.1 : Measure (Value i × unitInterval)).prod volume).map
    (Prod.fst ∘ Prod.fst))=lowerMeasure i
  rw [← Measure.map_map measurable_fst measurable_fst,Measure.map_fst_prod,
    measure_univ,one_smul,pi.property]

theorem lowerDraw_original_pair_law (i : Row) (pi : Joint i) :
    (lowerDrawLaw i pi).map Prod.fst=(pi.1 : Measure (Value i × unitInterval)) := by
  rw [lowerDrawLaw,Measure.map_fst_prod,measure_univ,one_smul]

def projectRival (i : Row) (eps : unitInterval) : RivalDraw i → Fin 3 × Bid i :=
  Prod.map id (drawBid i eps)

lemma measurable_projectRival (i : Row) (eps : unitInterval) :
    Measurable (projectRival i eps) :=
  measurable_id.prodMap (measurable_drawBid i eps)

theorem projectRival_law (i : Row) (eps : unitInterval) (pi : Joint i) :
    (rivalDrawLaw i pi).map (projectRival i eps)=
      (FiniteLaw.probabilityMeasure (categoryLaw i)).prod
        ((restrictedLaw i (eps,pi)).bidLaw : Measure (Bid i)) := by
  rw [rivalDrawLaw,projectRival,← Measure.map_prod_map _ _ measurable_id
    (measurable_drawBid i eps),Measure.map_id,lowerDraw_bid_law]

def drawRow (i : Row) (N : ℕ) (eps : unitInterval)
    (x : Fin N → RivalDraw i) : (Fin N → Fin 3) × (Fin N → Bid i) :=
  (fun j => (x j).1,fun j => drawBid i eps (x j).2)

lemma measurable_drawRow (i : Row) (N : ℕ) (eps : unitInterval) :
    Measurable (drawRow i N eps) :=
  (measurable_pi_lambda _ (fun j => measurable_fst.comp (measurable_pi_apply j))).prodMk
    (measurable_pi_lambda _ (fun j => (measurable_drawBid i eps).comp
      (measurable_snd.comp (measurable_pi_apply j))))

theorem drawRow_law (i : Row) (N : ℕ) (eps : unitInterval) (pi : Joint i) :
    (Measure.pi (fun _ : Fin N => rivalDrawLaw i pi)).map (drawRow i N eps)=
      (FiniteLaw.probabilityMeasure (categoryRowLaw i N)).prod
        (rowLaw N (restrictedLaw i (eps,pi)).bidLaw : Measure (Fin N → Bid i)) := by
  let e := MeasurableEquiv.arrowProdEquivProdArrow (Fin 3) (Bid i) (Fin N)
  let p : (Fin N → RivalDraw i) → (Fin N → Fin 3 × Bid i) :=
    fun x j => projectRival i eps (x j)
  have hp : Measurable p := measurable_pi_lambda _
    (fun j => (measurable_projectRival i eps).comp (measurable_pi_apply j))
  have hmap := measurePreserving_arrowProdEquivProdArrow (Fin 3) (Bid i) (Fin N)
    (fun _ => FiniteLaw.probabilityMeasure (categoryLaw i))
    (fun _ => ((restrictedLaw i (eps,pi)).bidLaw : Measure (Bid i)))
  change (Measure.pi (fun _ : Fin N => rivalDrawLaw i pi)).map (e ∘ p)=_
  rw [← Measure.map_map e.measurable hp,
    Measure.pi_map_pi (fun _ => (measurable_projectRival i eps).aemeasurable)]
  simp only [projectRival_law]
  rw [hmap.map_eq,categoryRowLaw,LowBody.probabilityMeasure_iid,rowLaw_eq_pi]

theorem integral_drawRow (i : Row) (N : ℕ) (eps : unitInterval) (pi : Joint i)
    (f : ((Fin N → Fin 3) × (Fin N → Bid i)) → ℝ)
    (hf : Measurable f) (C : ℝ) (hC : ∀p, |f p|≤ C) :
    (∫x, f (drawRow i N eps x) ∂Measure.pi (fun _ : Fin N => rivalDrawLaw i pi))=
      (categoryRowLaw i N).expect (fun kind =>
        ∫b : Fin N → Bid i, f (kind,b)
          ∂(rowLaw N (restrictedLaw i (eps,pi)).bidLaw : Measure (Fin N → Bid i))) := by
  have hi : Integrable f ((FiniteLaw.probabilityMeasure (categoryRowLaw i N)).prod
      (rowLaw N (restrictedLaw i (eps,pi)).bidLaw : Measure (Fin N → Bid i))) :=
    Integrable.of_bound hf.aestronglyMeasurable C
      (ae_of_all _ (fun p => by simpa only [Real.norm_eq_abs] using hC p))
  rw [← integral_map (measurable_drawRow i N eps).aemeasurable hf.aestronglyMeasurable,
    drawRow_law,integral_prod _ hi,LowBody.integral_probabilityMeasure]

theorem expectedUtility_eq_original_draws (i : Row) (N : ℕ)
    (eps : unitInterval) (pi : Joint i) (v : Value i) (q : unitInterval) :
    expectedUtility i N eps pi v q =
      ∫x : Fin N → RivalDraw i, (∫z : unitInterval,
        rowPayoff i (restrictedLaw i (eps,pi))
          (focalRow (fun j => (x j).1)) v
          (focalBids i (fun j => (x j).1) (drawBid i eps ((v,q),z))
            (fun j => drawBid i eps (x j).2)) 0)
        ∂Measure.pi (fun _ : Fin N => rivalDrawLaw i pi) := by
  let f : ((Fin N → Fin 3) × (Fin N → Bid i)) → ℝ := fun p =>
    ∫z : unitInterval, rowPayoff i (restrictedLaw i (eps,pi)) (focalRow p.1) v
      (focalBids i p.1 (drawBid i eps ((v,q),z)) p.2) 0
  have hf : Measurable f := by
    apply measurable_from_prod_countable_right
    intro kind
    exact (ActualSurplus.measurable_noisy_row i eps pi v q kind).stronglyMeasurable.integral_prod_right'.measurable
  have hb (p) : |f p|≤3*(v:ℝ) := by
    simpa only [f,drawBid,Real.norm_eq_abs,probReal_univ,mul_one] using
      norm_integral_le_of_norm_le_const
        (f := fun z : unitInterval => rowPayoff i (restrictedLaw i (eps,pi)) (focalRow p.1) v
          (focalBids i p.1 (noisyBid i (eps,((v,q),z))) p.2) 0)
        (C := 3*(v:ℝ))
        (ae_of_all (volume : Measure unitInterval) (fun z => by
          simpa only [Real.norm_eq_abs] using noisyRowPayoff_bound i eps pi v q z p.1 p.2))
  simpa only [expectedUtility,f,drawRow,drawBid] using
    (integral_drawRow i N eps pi f hf (3*(v:ℝ)) hb).symm

theorem rival_lower_bid_event (i : Row) (eps : unitInterval) (pi : Joint i)
    (s : Set (Bid i)) (hs : MeasurableSet s) :
    (rivalDrawLaw i pi) {x | x.1=0 ∧ drawBid i eps x.2∈s}=
      ENNReal.ofReal (Uniform05.t i) *
        ((restrictedLaw i (eps,pi)).bidLaw : Measure (Bid i)) s := by
  have he : {x : RivalDraw i | x.1=0 ∧ drawBid i eps x.2∈s}=
      ({0} : Set (Fin 3)) ×ˢ ((drawBid i eps) ⁻¹' s) := by ext x; simp
  rw [he,rivalDrawLaw,Measure.prod_prod,
    ← Measure.map_apply (measurable_drawBid i eps) hs,lowerDraw_bid_law]
  congr 1
  simp [FiniteLaw.probabilityMeasure,categoryLaw,Fin.sum_univ_succ]

theorem rival_lower_original_value_event (i : Row) (pi : Joint i)
    (s : Set (Value i)) (hs : MeasurableSet s) :
    (rivalDrawLaw i pi) {x | x.1=0 ∧ x.2.1.1∈s}=
      ENNReal.ofReal (Uniform05.t i) * lowerMeasure i s := by
  have hm : Measurable (fun x : LowerDraw i => x.1.1) := measurable_fst.comp measurable_fst
  have he : {x : RivalDraw i | x.1=0 ∧ x.2.1.1∈s}=
      ({0} : Set (Fin 3)) ×ˢ ((fun x : LowerDraw i => x.1.1) ⁻¹' s) := by ext x; simp
  rw [he,rivalDrawLaw,Measure.prod_prod,← Measure.map_apply hm hs,lowerDraw_value_law]
  congr 1
  simp [FiniteLaw.probabilityMeasure,categoryLaw,Fin.sum_univ_succ]

end FCAppendix.Affine.UniformFinite
