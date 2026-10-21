import FCAppendix.Affine.Tail04.OriginalActiveCompression
import FCAppendix.Affine.Tail04.LatentSpeciesCalculus
import FCAppendix.Affine.Tail04.NoisyNativeFiberProduct

noncomputable section
namespace FCAppendix.Affine.Tail04.NativeActiveCompressedLaw
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open Existence.Distributional OriginalValues CompactSourceBidLaws
open SourceTailNoisyFixedPoint NativeNoisySource LatentNoisyPopulation
open OriginalActiveCompression ActivePhysicalPayoff LatentSpeciesCalculus
open scoped BigOperators

def focalDistinct (Ds : FiniteTailNoisyGame.Data) {N : ℕ} {X : Type*}
    (tag : X→Fin 4) (decode : X→Icc (1:ℝ) Ds.B)
    (b : Icc (1:ℝ) Ds.B) (row : Fin N→X) : Prop :=
  ∀ i j : Fin (Ds.count (tags tag row) 1+1),i≠j→
    (focalRow Ds (tags tag row) decode b row i:ℝ)≠
      (focalRow Ds (tags tag row) decode b row j:ℝ)

variable (D : FiniteTailNoisyGame.Data) (P : ValueParameters) (t : ℝ) (ht : P.M< t)
  (πL : Law (A:=LowBody.LowValue P.d0) P.originalLowLaw)
  (π : JointProfile D P t ht) (upperBid : ℝ→ℝ) (hupperBid : Measurable upperBid)
  (hdR : P.d0< D.R) (H : ℝ) (hBH : D.B< H) (hfloor : ∀ v,t< v→ H≤ upperBid v)
  (N : ℕ)
  (hrare : (1-D.ξ)*D.B+D.ξ*D.B*((N+1:ℕ)*
    (tailMass P t/(partialMass+tailMass P t)))≤ D.R)

def partialLaw : ProbabilityMeasure (Icc (installOriginal D P t ht).R (installOriginal D P t ht).Up) := bidMarginal (π 2).1

def latentTag (z : Draw) : Fin 4 := (regions D P hdR H hBH).coarseTag (realize D z)
def latentBid (z : Draw) : Icc (1:ℝ) D.B :=
  NoisyNativeFiberProduct.commonProjection D P hdR H hBH (realize D z)

lemma measurable_latentTag : Measurable (latentTag D P hdR H hBH) :=
  (regions D P hdR H hBH).measurable_coarseTag.comp (measurable_realize D)

lemma measurable_latentBid : Measurable (latentBid D P hdR H hBH) :=
  (NoisyNativeFiberProduct.measurable_commonProjection D P hdR H hBH).comp (measurable_realize D)

include hfloor hrare in
include t ht πL π upperBid hupperBid hfloor N hrare in
theorem original_category_mass (k : Fin 4) :
    (drawLaw D P t ht πL π upperBid hupperBid) (latentTag D P hdR H hBH ⁻¹' {k})=ENNReal.ofReal ((installOriginal D P t ht).categories.mass k) := by
  change (drawLaw D P t ht πL π upperBid hupperBid) ((realize D) ⁻¹' ((regions D P hdR H hBH).coarseTag ⁻¹' {k}))=_
  rw [←Measure.map_apply (measurable_realize D) ((regions D P hdR H hBH).measurable_coarseTag (measurableSet_singleton k)),
    realize_original_user D P t ht πL π upperBid hupperBid hdR H hBH hfloor (N+1) hrare]
  exact NoisyNativeCategories.native_source_category_mass D P t ht hdR H hBH πL π
    upperBid hupperBid hfloor (NativeNoisySource.game D P t ht hdR H hBH πL π upperBid hupperBid hfloor (N+1) hrare)
      (game_original_joint D P t ht hdR H hBH πL π upperBid hupperBid hfloor (N+1) hrare) k

include hfloor hrare in
include t ht πL π upperBid hupperBid hfloor N hrare in
theorem original_category_ne_zero (k : Fin 4) : (drawLaw D P t ht πL π upperBid hupperBid) (latentTag D P hdR H hBH ⁻¹' {k})≠0 := by
  rw [original_category_mass D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare]
  exact (ENNReal.ofReal_pos.mpr (NoisyNativeCategories.source_category_positive P t ht k)).ne'

include hfloor hrare in
include t ht πL π upperBid hupperBid hfloor N hrare in
theorem original_common_projection :
    (cond (drawLaw D P t ht πL π upperBid hupperBid) (latentTag D P hdR H hBH ⁻¹' {1})).map (latentBid D P hdR H hBH)=
      (ProbabilityMeasure.toMeasure (bidMarginal (activePhysical D P t ht π).1)) := by
  change (cond (drawLaw D P t ht πL π upperBid hupperBid) ((realize D) ⁻¹' ((regions D P hdR H hBH).coarseTag ⁻¹' {1}))).map
    ((NoisyNativeFiberProduct.commonProjection D P hdR H hBH) ∘ realize D)=_
  rw [←Measure.map_map (NoisyNativeFiberProduct.measurable_commonProjection D P hdR H hBH)
      (measurable_realize D),map_cond_preimage (drawLaw D P t ht πL π upperBid hupperBid) (realize D) (measurable_realize D)
        _ ((regions D P hdR H hBH).measurable_coarseTag (measurableSet_singleton 1)),
    realize_original_user D P t ht πL π upperBid hupperBid hdR H hBH hfloor (N+1) hrare]
  exact NoisyNativeFiberProduct.common_projection_law D P t ht hdR H hBH πL π
    upperBid hupperBid hfloor N (by
      simpa only [Nat.cast_add,Nat.cast_one,SourceTailNoisyFixedPoint.tailMass] using hrare)

def physicalValue (v : ℝ) (b : Icc (1:ℝ) D.B) (row : Fin N→ Draw) : ℝ :=
  rivalValue (installOriginal D P t ht) (latentTag D P hdR H hBH) (latentBid D P hdR H hBH) (partialLaw D P t ht π) v b row

lemma measurable_physicalValue (v : ℝ) (b : Icc (1:ℝ) D.B) :
    Measurable (physicalValue D P t ht π hdR H hBH N v b) :=
  measurable_rivalValue (installOriginal D P t ht) _ _ (partialLaw D P t ht π) (measurable_latentTag D P hdR H hBH)
    (measurable_latentBid D P hdR H hBH) v b

lemma measurable_physicalValue_joint :
    Measurable (fun z : (ℝ×Icc (1:ℝ) D.B)×(Fin N→ Draw) =>
      physicalValue D P t ht π hdR H hBH N z.1.1 z.1.2 z.2) :=
  measurable_rivalValue_joint (installOriginal D P t ht) _ _ (partialLaw D P t ht π) (measurable_latentTag D P hdR H hBH)
    (measurable_latentBid D P hdR H hBH)

lemma physicalValue_bound (v : ℝ) (b : Icc (1:ℝ) D.B) (row : Fin N→ Draw) :
    |physicalValue D P t ht π hdR H hBH N v b row|≤|v|+2*D.B :=
  rivalValue_bound (installOriginal D P t ht) _ _ (partialLaw D P t ht π) v b row

include hfloor hrare in
include πL upperBid hupperBid hfloor hrare in
theorem physicalValue_integral (v : ℝ) (b : Icc (1:ℝ) D.B) :
    (∫ row,physicalValue D P t ht π hdR H hBH N v b row
      ∂Measure.pi (fun _ : Fin N => (drawLaw D P t ht πL π upperBid hupperBid)))=
      ∑ kind : Fin N→ Fin 4,(CommonList.iid (installOriginal D P t ht).categories N).mass kind*
        ∫ row : Fin ((installOriginal D P t ht).count kind 1)→ Icc (1:ℝ) D.B,
          regimeValue (installOriginal D P t ht) ((installOriginal D P t ht).count kind 1) ((installOriginal D P t ht).count kind 2) ((installOriginal D P t ht).count kind 3) (partialLaw D P t ht π) v
            (decide (0< (installOriginal D P t ht).count kind 0)) (Fin.cons b row)
          ∂Measure.pi (fun _ : Fin ((installOriginal D P t ht).count kind 1) => (ProbabilityMeasure.toMeasure (bidMarginal (activePhysical D P t ht π).1))) :=
  original_rivalValue_integral (installOriginal D P t ht) (drawLaw D P t ht πL π upperBid hupperBid) (latentTag D P hdR H hBH) (measurable_latentTag D P hdR H hBH)
    (latentBid D P hdR H hBH) (measurable_latentBid D P hdR H hBH)
    (original_category_ne_zero D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare)
    (bidMarginal (activePhysical D P t ht π).1) (original_common_projection D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare) (partialLaw D P t ht π)
    (original_category_mass D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare) v b

include hfloor hrare in
include πL upperBid hupperBid hfloor hrare in
theorem original_noisy_physicalValue (v : ℝ) (b : Icc (1:ℝ) D.U) :
    (∫ u : unitInterval,∫ row,physicalValue D P t ht π hdR H hBH N v
      (noisyBid (by norm_num : (0:ℝ)<1) D.heps.le (b,u)) row
        ∂Measure.pi (fun _ : Fin N => (drawLaw D P t ht πL π upperBid hupperBid)))=
      (installOriginal D P t ht).activeExpected N (bidLaws D P t ht π,(v,b)) := by
  have hi (kind : Fin N→ Fin 4) : Integrable (fun u : unitInterval =>
      ∫ row : Fin ((installOriginal D P t ht).count kind 1)→ Icc (1:ℝ) D.B,
        regimeValue (installOriginal D P t ht) ((installOriginal D P t ht).count kind 1) ((installOriginal D P t ht).count kind 2) ((installOriginal D P t ht).count kind 3) (partialLaw D P t ht π) v
          (decide (0< (installOriginal D P t ht).count kind 0))
          (Fin.cons (noisyBid (by norm_num : (0:ℝ)<1) D.heps.le (b,u)) row)
        ∂Measure.pi (fun _ : Fin ((installOriginal D P t ht).count kind 1) => (ProbabilityMeasure.toMeasure (bidMarginal (activePhysical D P t ht π).1)))) volume := by
    rw [NoisyCommonRowLaw.original_common_noisy_law D P t ht π]
    exact ActivePhysicalPayoff.integrable_focal_average (installOriginal D P t ht) _ _ _ (partialLaw D P t ht π) v _ b
      ((installOriginal D P t ht).commonLaw (bidLaws D P t ht π))
  simp_rw [physicalValue_integral D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare]
  erw [integral_finsetSum (Finset.univ : Finset (Fin N→Fin 4))
    (fun kind _ => (hi kind).const_mul ((CommonList.iid (installOriginal D P t ht).categories N).mass kind))]
  simp_rw [integral_const_mul]
  unfold FiniteTailNoisyGame.Data.activeExpected
  apply Finset.sum_congr rfl
  intro kind _
  congr 1
  erw [NoisyCommonRowLaw.original_common_noisy_law D P t ht π,
    ActivePhysicalPayoff.split_focal_integral]
  erw [LowBody.rowLaw_eq_measure_pi]
  rfl

include hfloor hrare in
include t ht πL π upperBid hupperBid hfloor hrare in
theorem ae_original_focal_distinct (b : Icc (1:ℝ) D.B) :
    ∀ᵐ row ∂Measure.pi (fun _ : Fin N => (drawLaw D P t ht πL π upperBid hupperBid)),
      ∀ i j : Fin ((installOriginal D P t ht).count (tags (latentTag D P hdR H hBH) row) 1+1),i≠j→
        (focalRow (installOriginal D P t ht) (tags (latentTag D P hdR H hBH) row)
          (latentBid D P hdR H hBH) b row i:ℝ)≠
        (focalRow (installOriginal D P t ht) (tags (latentTag D P hdR H hBH) row)
          (latentBid D P hdR H hBH) b row j:ℝ) := by
  apply ae_of_all_category_fibers (drawLaw D P t ht πL π upperBid hupperBid) (latentTag D P hdR H hBH)
    (measurable_latentTag D P hdR H hBH)
  intro kind
  have hp : MeasurePreserving (commonRow (installOriginal D P t ht) kind (latentBid D P hdR H hBH))
      (Measure.pi (fun i => cond (drawLaw D P t ht πL π upperBid hupperBid) (latentTag D P hdR H hBH ⁻¹' {kind i})))
      (Measure.pi (fun _ : Fin ((installOriginal D P t ht).count kind 1) => (ProbabilityMeasure.toMeasure (bidMarginal (activePhysical D P t ht π).1)))) :=
    by
      refine ⟨measurable_commonRow (installOriginal D P t ht) kind
        (latentBid D P hdR H hBH) (measurable_latentBid D P hdR H hBH),?_⟩
      exact commonRow_law (installOriginal D P t ht) (drawLaw D P t ht πL π upperBid hupperBid) (latentTag D P hdR H hBH)
        (latentBid D P hdR H hBH) (measurable_latentBid D P hdR H hBH)
        (original_category_ne_zero D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare)
        (bidMarginal (activePhysical D P t ht π).1) (original_common_projection D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare) kind
  have hd : ∀ᵐ (r : Fin ((installOriginal D P t ht).count kind 1)→Icc (1:ℝ) D.B)
      ∂Measure.pi (fun _ : Fin ((installOriginal D P t ht).count kind 1) => (ProbabilityMeasure.toMeasure (bidMarginal (activePhysical D P t ht π).1))),
      ∀ i j : Fin ((installOriginal D P t ht).count kind 1+1),i≠j→
        (Fin.cons (α:=fun _=>Icc (1:ℝ) D.B) b r i:ℝ)≠
          (Fin.cons (α:=fun _=>Icc (1:ℝ) D.B) b r j:ℝ) := by
    rw [NoisyCommonRowLaw.original_common_noisy_law D P t ht π]
    have hh := OriginalNoiseProduct.ae_cons_physicalRow_distinct (by norm_num : (0:ℝ)<1) D.heps
      ((installOriginal D P t ht).count kind 1) ((installOriginal D P t ht).commonLaw (bidLaws D P t ht π)) b
    filter_upwards [hh] with r hr
    have he (q : Fin ((installOriginal D P t ht).count kind 1+1)) :
        (Fin.cons (α:=fun _=>Icc (1:ℝ) D.B) b r q:ℝ)=
          Fin.cons (α:=fun _=>ℝ) (b:ℝ) (fun k => (r k:ℝ)) q := by
      refine Fin.cases rfl (fun _ => rfl) q
    intro i j hij
    rw [he,he]
    exact hr i j hij
  have ht' := ae_tags_conditional (drawLaw D P t ht πL π upperBid hupperBid) (latentTag D P hdR H hBH)
    (measurable_latentTag D P hdR H hBH)
    (original_category_ne_zero D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare) kind
  filter_upwards [ht',hp.quasiMeasurePreserving.ae hd] with row hrow hd
  subst kind
  exact hd

include hfloor hrare in
include t ht πL π upperBid hupperBid hfloor hrare in
theorem ae_original_carrier_distinct (J : Set Draw) :
    ∀ᵐ z ∂((drawLaw D P t ht πL π upperBid hupperBid).restrict J).prod
      (Measure.pi (fun _ : Fin N => drawLaw D P t ht πL π upperBid hupperBid)),
      focalDistinct (installOriginal D P t ht) (latentTag D P hdR H hBH)
        (latentBid D P hdR H hBH) (latentBid D P hdR H hBH z.1) z.2 :=
by
  let Ds := installOriginal D P t ht
  let tag := latentTag D P hdR H hBH
  let decode := latentBid D P hdR H hBH
  let μ := drawLaw D P t ht πL π upperBid hupperBid
  let p : Draw×(Fin N→Draw)→Prop := fun z =>
    ∀ kind : Fin N→Fin 4,tags tag z.2=kind→
      ∀ i j : Fin (Ds.count kind 1+1),i≠j→
        (focalRow Ds kind decode (decode z.1) z.2 i:ℝ)≠
          (focalRow Ds kind decode (decode z.1) z.2 j:ℝ)
  have hdecode : Measurable decode := measurable_latentBid D P hdR H hBH
  have hp : MeasurableSet {z | p z} := by
    dsimp only [p]
    rw [setOf_forall]
    apply MeasurableSet.iInter
    intro kind
    refine MeasurableSet.imp
      (measurableSet_eq_fun
        ((measurable_tags tag (measurable_latentTag D P hdR H hBH)).comp measurable_snd)
        measurable_const) ?_
    rw [setOf_forall]
    apply MeasurableSet.iInter
    intro i
    rw [setOf_forall]
    apply MeasurableSet.iInter
    intro j
    apply MeasurableSet.imp (MeasurableSet.const _)
    have hr := (measurable_focalRow Ds kind decode hdecode).comp
      ((hdecode.comp measurable_fst).prodMk measurable_snd)
    exact (measurableSet_eq_fun
      (measurable_subtype_coe.comp ((measurable_pi_apply i).comp hr))
      (measurable_subtype_coe.comp ((measurable_pi_apply j).comp hr))).compl
  have ha : ∀ᵐ z ∂(μ.restrict J).prod (Measure.pi (fun _ : Fin N => μ)),p z := by
    apply (Measure.ae_prod_iff_ae_ae hp).2
    exact ae_of_all _ fun x =>
      (ae_original_focal_distinct D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare
        (decode x)).mono fun row h kind hk => by
          subst kind
          exact h
  filter_upwards [ha] with z hz
  exact hz (tags tag z.2) rfl

end FCAppendix.Affine.Tail04.NativeActiveCompressedLaw
