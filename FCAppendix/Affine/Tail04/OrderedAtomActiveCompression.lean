import FCAppendix.Affine.Tail04.ActivePhysicalPayoff
import FCAppendix.Affine.Tail04.OrderedFiniteTailNoisyGame
import FCAppendix.Affine.Tail04.OriginalFiniteFibers
import FCAppendix.Affine.Tail04.PrivateConditionalRows

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedAtomActiveCompression
open MeasureTheory ProbabilityTheory Set Classical
open FiniteTailNoisyGame CompactSourceBidLaws ActivePhysicalPayoff
open OriginalFiniteFibers PrivateConditionalRows
open scoped BigOperators

section Measures
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem map_cond_preimage (μ : Measure X) (f : X→ Y) (hf : Measurable f)
    (E : Set Y) (hE : MeasurableSet E) :
    (cond μ (f ⁻¹' E)).map f=cond (μ.map f) E := by
  ext B hB
  rw [Measure.map_apply hf hB,cond_apply (hE.preimage hf),cond_apply hE,
    Measure.map_apply hf hE,Measure.map_apply hf (hE.inter hB)]
  rfl

end Measures

theorem ae_of_all_category_fibers {X : Type*} [MeasurableSpace X] {N : ℕ}
    (μ : Measure X) [IsProbabilityMeasure μ] (tag : X→ Fin 4) (htag : Measurable tag)
    (Q : (Fin N→ X)→ Prop)
    (hQ : ∀ kind : Fin N→ Fin 4,
      ∀ᵐ row ∂Measure.pi (fun i => cond μ (tag ⁻¹' {kind i})),Q row) :
    ∀ᵐ row ∂Measure.pi (fun _ : Fin N => μ),Q row := by
  rw [ae_iff]
  rw [iid_finite_disintegration μ tag htag,measure_sum_apply]
  apply Finset.sum_eq_zero
  intro kind _
  rw [Measure.smul_apply,show (Measure.pi (fun i => cond μ (tag ⁻¹' {kind i})))
    {row | ¬Q row}=0 from ae_iff.mp (hQ kind)]
  simp

section Coordinates
variable (D : Data) {N : ℕ} (kind : Fin N→ Fin 4)

lemma count_eq_card (k : Fin 4) : D.count kind k=Fintype.card {i : Fin N // kind i=k} := by
  simp only [Data.count,Fintype.card_subtype]

def enumeration (k : Fin 4) : Fin (D.count kind k)≃{i : Fin N // kind i=k} :=
  (finCongr (count_eq_card D kind k)).trans (Fintype.equivFin _).symm

variable {X : Type*} [MeasurableSpace X] (tag : X→ Fin 4) (decode : X→ Icc (1:ℝ) D.B)

def tags (row : Fin N→ X) : Fin N→ Fin 4 := tag ∘ row

lemma measurable_tags (htag : Measurable tag) : Measurable (tags tag (N:=N)) :=
  measurable_pi_lambda _ (fun i => htag.comp (measurable_pi_apply i))

def commonRow (row : Fin N→ X) : Fin (D.count kind 1)→ Icc (1:ℝ) D.B :=
  fun j => decode (row (enumeration D kind 1 j).val)

lemma measurable_commonRow (hdecode : Measurable decode) :
    Measurable (commonRow D kind decode) :=
  measurable_pi_lambda _ (fun j => hdecode.comp (measurable_pi_apply (enumeration D kind 1 j).val))

def focalRow (b : Icc (1:ℝ) D.B) (row : Fin N→ X) :
    Fin (D.count kind 1+1)→ Icc (1:ℝ) D.B :=
  Fin.cons b (commonRow D kind decode row)

lemma measurable_focalRow (hdecode : Measurable decode) : Measurable (fun z : Icc (1:ℝ) D.B×(Fin N→ X) =>
    focalRow D kind decode z.1 z.2) := by
  apply measurable_pi_lambda
  intro j
  refine Fin.cases measurable_fst (fun k => ?_) j
  exact ((measurable_pi_apply k).comp (measurable_commonRow D kind decode hdecode)).comp measurable_snd

end Coordinates

section Integrand
variable (D : Data) {N : ℕ} {X : Type*} [MeasurableSpace X]
    (tag : X→ Fin 4) (decode : X→ Icc (1:ℝ) D.B)
    (μP : ProbabilityMeasure (Icc D.R D.Up))

def caseValue (kind : Fin N→ Fin 4) (v : ℝ) (b : Icc (1:ℝ) D.B) (row : Fin N→ X) : ℝ :=
  regimeValue D (D.count kind 1) (min (D.count kind 2) (D.count kind 3)) (max (D.count kind 2) (D.count kind 3)) μP v
    (decide (0< D.count kind 0)) (focalRow D kind decode b row)

def rivalValue (v : ℝ) (b : Icc (1:ℝ) D.B) (row : Fin N→ X) : ℝ :=
  caseValue D decode μP (tags tag row) v b row

lemma measurable_caseValue (hdecode : Measurable decode) (kind : Fin N→ Fin 4)
    (v : ℝ) (b : Icc (1:ℝ) D.B) : Measurable (caseValue D decode μP kind v b) := by
  apply (measurable_regimeValue D (D.count kind 1) (min (D.count kind 2) (D.count kind 3)) (max (D.count kind 2) (D.count kind 3))
    μP v (decide (0< D.count kind 0))).comp
  exact measurable_pi_lambda _ fun j =>
    Fin.cases measurable_const (fun k => (measurable_pi_apply k).comp
      (measurable_commonRow D kind decode hdecode)) j

lemma measurable_rivalValue (htag : Measurable tag) (hdecode : Measurable decode)
    (v : ℝ) (b : Icc (1:ℝ) D.B) : Measurable (rivalValue D tag decode μP (N:=N) v b) := by
  change Measurable (fun row : Fin N→X => caseValue D decode μP (tags tag row) v b row)
  exact LocalCoordinates.measurable_finite_eval (tags tag (N:=N))
    (fun (row : Fin N→X) (kind : Fin N→Fin 4) => caseValue D decode μP kind v b row)
    (measurable_tags tag htag)
    (fun kind => measurable_caseValue D decode μP hdecode kind v b)

lemma measurable_caseValue_joint (hdecode : Measurable decode) (kind : Fin N→ Fin 4) :
    Measurable (fun z : (ℝ×Icc (1:ℝ) D.B)×(Fin N→ X) =>
      caseValue D decode μP kind z.1.1 z.1.2 z.2) := by
  have hb : Measurable (fun z : (ℝ×Icc (1:ℝ) D.B)×(Fin N→ X) =>
      focalRow D kind decode z.1.2 z.2) :=
    (measurable_focalRow D kind decode hdecode).comp (measurable_fst.snd.prodMk measurable_snd)
  have hv (reg : Bool) : Measurable (fun z : (ℝ×Icc (1:ℝ) D.B)×(Fin N→ X) =>
      ActivePhysicalPayoff.value D (D.count kind 1) (min (D.count kind 2) (D.count kind 3)) (max (D.count kind 2) (D.count kind 3)) μP
        z.1.1 reg (decide (0< D.count kind 0)) (focalRow D kind decode z.1.2 z.2)) := by
    unfold ActivePhysicalPayoff.value affineCountUtility CountLaw.utility FiniteLaw.expect
    apply Finset.measurable_sum
    intro r _
    apply ((ActivePhysicalPayoff.measurable_mass D (D.count kind 1) (min (D.count kind 2) (D.count kind 3))
      (max (D.count kind 2) (D.count kind 3)) μP reg (decide (0< D.count kind 0)) r).comp hb).mul
    unfold userPayoff
    exact ((measurable_fst.fst.mul measurable_const).sub
      ((((measurable_pi_apply 0).comp hb).subtype_val).mul measurable_const)).sub measurable_const
  exact ((hv false).const_mul _).add ((hv true).const_mul _)

lemma measurable_rivalValue_joint (htag : Measurable tag) (hdecode : Measurable decode) :
    Measurable (fun z : (ℝ×Icc (1:ℝ) D.B)×(Fin N→ X) =>
      rivalValue D tag decode μP z.1.1 z.1.2 z.2) := by
  change Measurable (fun z : (ℝ×Icc (1:ℝ) D.B)×(Fin N→ X) =>
    caseValue D decode μP (tags tag z.2) z.1.1 z.1.2 z.2)
  exact LocalCoordinates.measurable_finite_eval
    (fun z : (ℝ×Icc (1:ℝ) D.B)×(Fin N→X) => tags tag z.2)
    (fun (z : (ℝ×Icc (1:ℝ) D.B)×(Fin N→X)) (kind : Fin N→Fin 4) =>
      caseValue D decode μP kind z.1.1 z.1.2 z.2)
    ((measurable_tags tag htag).comp measurable_snd)
    (fun kind => measurable_caseValue_joint D decode μP hdecode kind)

omit [MeasurableSpace X] in
lemma caseValue_bound (kind : Fin N→ Fin 4) (v : ℝ) (b : Icc (1:ℝ) D.B) (row : Fin N→ X) :
    |caseValue D decode μP kind v b row|≤|v|+2*D.B :=
  regimeValue_bound D (D.count kind 1) (min (D.count kind 2) (D.count kind 3)) (max (D.count kind 2) (D.count kind 3)) μP v _ _

omit [MeasurableSpace X] in
lemma rivalValue_bound (v : ℝ) (b : Icc (1:ℝ) D.B) (row : Fin N→ X) :
    |rivalValue D tag decode μP v b row|≤|v|+2*D.B :=
  caseValue_bound D decode μP _ v b row

lemma integrable_rivalValue (htag : Measurable tag) (hdecode : Measurable decode)
    (ν : Measure (Fin N→ X)) [IsFiniteMeasure ν] (v : ℝ) (b : Icc (1:ℝ) D.B) :
    Integrable (rivalValue D tag decode μP v b) ν :=
  Integrable.of_bound (measurable_rivalValue D tag decode μP htag hdecode v b).aestronglyMeasurable
    (|v|+2*D.B) (ae_of_all _ (fun row => by
      rw [Real.norm_eq_abs]
      exact rivalValue_bound D tag decode μP v b row))

end Integrand

section ConditionalLaw
variable (D : Data) {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (tag : X→ Fin 4) (htag : Measurable tag)
    (decode : X→ Icc (1:ℝ) D.B) (hdecode : Measurable decode)
    (hmass : ∀ k,μ (tag ⁻¹' {k})≠0)
    (ρ : ProbabilityMeasure (Icc (1:ℝ) D.B))
    (hρ : (cond μ (tag ⁻¹' {1})).map decode=(ρ : Measure _))
    (μP : ProbabilityMeasure (Icc D.R D.Up)) {N : ℕ}

include hdecode hmass hρ in
theorem commonRow_law (kind : Fin N→ Fin 4) :
    (Measure.pi (fun i => cond μ (tag ⁻¹' {kind i}))).map (commonRow D kind decode)=
      Measure.pi (fun _ : Fin (D.count kind 1) => (ρ : Measure _)) := by
  classical
  letI (i : Fin N) : Decidable (kind i=1) := Classical.propDecidable _
  let ν : Fin N→ Measure X := fun i => cond μ (tag ⁻¹' {kind i})
  haveI (i : Fin N) : IsProbabilityMeasure (ν i) := cond_isProbabilityMeasure (hmass (kind i))
  have hh := blockSplit_law ν (fun i => kind i=1) (D.count kind 1) (enumeration D kind 1)
    decode hdecode (ρ : Measure _) (fun j => by
      simpa only [ν,(enumeration D kind 1 j).property] using hρ)
  have hp := congrArg (fun η => η.map Prod.fst) hh
  rw [Measure.map_map measurable_fst (measurable_blockSplit _ _ _ _ hdecode)] at hp
  exact hp.trans (measurePreserving_fst
    (μ:=Measure.pi (fun _ : Fin (D.count kind 1) => (ρ : Measure (Icc (1:ℝ) D.B))))
    (ν:=Measure.pi (fun i : {i : Fin N // ¬kind i=1} => ν i))).map_eq

include htag hmass in
lemma ae_tags_conditional (kind : Fin N→ Fin 4) :
    ∀ᵐ row ∂Measure.pi (fun i => cond μ (tag ⁻¹' {kind i})),tags tag row=kind := by
  haveI (i : Fin N) : IsProbabilityMeasure (cond μ (tag ⁻¹' {kind i})) :=
    cond_isProbabilityMeasure (hmass (kind i))
  have hi (i : Fin N) : ∀ᵐ row ∂Measure.pi (fun j => cond μ (tag ⁻¹' {kind j})),tag (row i)=kind i :=
    (measurePreserving_eval (fun j => cond μ (tag ⁻¹' {kind j})) i).quasiMeasurePreserving.ae
      (ae_cond_mem (htag (measurableSet_singleton (kind i))))
  filter_upwards [ae_all_iff.mpr hi] with row hrow
  exact funext hrow

include htag hdecode hmass hρ in
theorem conditional_rivalValue_integral (kind : Fin N→ Fin 4)
    (v : ℝ) (b : Icc (1:ℝ) D.B) :
    (∫ row,rivalValue D tag decode μP v b row
      ∂Measure.pi (fun i => cond μ (tag ⁻¹' {kind i})))=
      ∫ row : Fin (D.count kind 1)→ Icc (1:ℝ) D.B,
        regimeValue D (D.count kind 1) (min (D.count kind 2) (D.count kind 3)) (max (D.count kind 2) (D.count kind 3)) μP v
          (decide (0< D.count kind 0)) (Fin.cons b row)
        ∂Measure.pi (fun _ : Fin (D.count kind 1) => (ρ : Measure _)) := by
  have hf : Measurable (fun row : Fin (D.count kind 1)→ Icc (1:ℝ) D.B =>
      regimeValue D (D.count kind 1) (min (D.count kind 2) (D.count kind 3)) (max (D.count kind 2) (D.count kind 3)) μP v
        (decide (0< D.count kind 0)) (Fin.cons b row)) :=
    (measurable_regimeValue D _ _ _ μP v _).comp
      (measurable_pi_lambda _ fun j => Fin.cases measurable_const (fun k => measurable_pi_apply k) j)
  calc
    _=∫ row,caseValue D decode μP kind v b row
        ∂Measure.pi (fun i => cond μ (tag ⁻¹' {kind i})) := by
      apply integral_congr_ae
      filter_upwards [ae_tags_conditional μ tag htag hmass kind] with row hrow
      simp only [rivalValue,hrow]
    _=_ := by
      rw [←commonRow_law D μ tag decode hdecode hmass ρ hρ kind,
        integral_map (measurable_commonRow D kind decode hdecode).aemeasurable hf.aestronglyMeasurable]
      rfl

include htag hdecode hmass hρ in
theorem original_rivalValue_integral
    (hcat : ∀ k,μ (tag ⁻¹' {k})=ENNReal.ofReal (D.categories.mass k))
    (v : ℝ) (b : Icc (1:ℝ) D.B) :
    (∫ row,rivalValue D tag decode μP (N:=N) v b row ∂Measure.pi (fun _ : Fin N => μ))=
      ∑ kind : Fin N→ Fin 4,(CommonList.iid D.categories N).mass kind*
        ∫ row : Fin (D.count kind 1)→ Icc (1:ℝ) D.B,
          regimeValue D (D.count kind 1) (min (D.count kind 2) (D.count kind 3)) (max (D.count kind 2) (D.count kind 3)) μP v
            (decide (0< D.count kind 0)) (Fin.cons b row)
          ∂Measure.pi (fun _ : Fin (D.count kind 1) => (ρ : Measure _)) := by
  classical
  haveI (kind : Fin N→ Fin 4) (i : Fin N) :
      IsProbabilityMeasure (cond μ (tag ⁻¹' {kind i})) := cond_isProbabilityMeasure (hmass (kind i))
  have hw (kind : Fin N→ Fin 4) : (∏ i,μ (tag ⁻¹' {kind i}))=
      ENNReal.ofReal ((CommonList.iid D.categories N).mass kind) := by
    simp_rw [hcat]
    exact (ENNReal.ofReal_prod_of_nonneg (fun i _ => D.categories.nonneg (kind i))).symm
  rw [iid_finite_disintegration μ tag htag]
  simp_rw [hw]
  rw [integral_finsetSum_measure (fun kind _ =>
    (integrable_rivalValue D tag decode μP htag hdecode _ v b).smul_measure ENNReal.ofReal_ne_top)]
  refine Finset.sum_congr (by ext; simp) ?_
  intro kind _
  rw [integral_smul_measure,ENNReal.toReal_ofReal ((CommonList.iid D.categories N).nonneg kind),
    conditional_rivalValue_integral D μ tag htag decode hdecode hmass ρ hρ μP kind v b]
  rfl

end ConditionalLaw
end FCAppendix.Affine.Tail04.OrderedAtomActiveCompression
