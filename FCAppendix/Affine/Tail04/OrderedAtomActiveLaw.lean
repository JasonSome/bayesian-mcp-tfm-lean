import FCAppendix.Affine.Tail04.OrderedAtomActiveCompression
import FCAppendix.Affine.Tail04.OrderedNativeBandCarrierIC
import FCAppendix.Affine.Tail04.NoisyNativeFiberProduct

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedAtomActiveLaw
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open Existence.Distributional OriginalValues CompactSourceBidLaws
open SourceTailNoisyFixedPoint NativeNoisySource LatentNoisyPopulation
open OrderedAtomActiveCompression ActivePhysicalPayoff LatentSpeciesCalculus
open scoped BigOperators

variable (D : FiniteTailNoisyGame.Data) (P : ValueParameters) (t : ℝ) (ht : P.M< t)
  (πL : Law (A:=LowBody.LowValue P.d0) P.originalLowLaw)
  (π : JointProfile D P t ht) (upperBid : ℝ→ℝ) (hupperBid : Measurable upperBid)
  (hdR : P.d0< D.R) (H : ℝ) (hBH : D.B< H) (hfloor : ∀ v,t< v→ H≤ upperBid v)
  (N : ℕ)
  (hrare : (1-D.ξ)*D.B+D.ξ*D.B*((N+1:ℕ)*
    (tailMass P t/(partialMass+tailMass P t)))≤ D.R)

local notation "Ds" => installOriginal D P t ht
local notation "E" => regions D P hdR H hBH
local notation "Γ" => NativeNoisySource.game D P t ht hdR H hBH πL π upperBid hupperBid hfloor (N+1) hrare
local notation "μ" => drawLaw D P t ht πL π upperBid hupperBid

private def activeRivalLaw : ProbabilityMeasure (Icc (1:ℝ) D.B) :=
  bidMarginal (activePhysical D P t ht π).1

private def partialRivalLaw : ProbabilityMeasure (Icc (installOriginal D P t ht).R (installOriginal D P t ht).Up) :=
  bidMarginal (π 2).1

local notation "ρA" => activeRivalLaw D P t ht π
local notation "μP" => partialRivalLaw D P t ht π

def latentTag (z : Draw) : Fin 4 := (E).coarseTag (realize D z)
def latentBid (z : Draw) : Icc (1:ℝ) D.B :=
  NoisyNativeFiberProduct.commonProjection D P hdR H hBH (realize D z)

lemma measurable_latentTag : Measurable (latentTag D P hdR H hBH) :=
  (E).measurable_coarseTag.comp (measurable_realize D)

lemma measurable_latentBid : Measurable (latentBid D P hdR H hBH) :=
  (NoisyNativeFiberProduct.measurable_commonProjection D P hdR H hBH).comp (measurable_realize D)

include hfloor hrare in
include t ht πL π upperBid hupperBid hfloor N hrare in
theorem original_category_mass (k : Fin 4) :
    μ (latentTag D P hdR H hBH ⁻¹' {k})=ENNReal.ofReal ((Ds).categories.mass k) := by
  change μ ((realize D) ⁻¹' ((E).coarseTag ⁻¹' {k}))=_
  rw [←Measure.map_apply (measurable_realize D) ((E).measurable_coarseTag (measurableSet_singleton k)),
    realize_original_user D P t ht πL π upperBid hupperBid hdR H hBH hfloor (N+1) hrare]
  exact NoisyNativeCategories.native_source_category_mass D P t ht hdR H hBH πL π
    upperBid hupperBid hfloor Γ
      (game_original_joint D P t ht hdR H hBH πL π upperBid hupperBid hfloor (N+1) hrare) k

include hfloor hrare in
include t ht πL π upperBid hupperBid hfloor N hrare in
theorem original_category_ne_zero (k : Fin 4) : μ (latentTag D P hdR H hBH ⁻¹' {k})≠0 := by
  rw [original_category_mass D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare]
  exact (ENNReal.ofReal_pos.mpr (NoisyNativeCategories.source_category_positive P t ht k)).ne'

include hfloor hrare in
include t ht πL π upperBid hupperBid hfloor N hrare in
theorem original_common_projection :
    (cond μ (latentTag D P hdR H hBH ⁻¹' {1})).map (latentBid D P hdR H hBH)=
      (ρA : Measure (Icc (1:ℝ) D.B)) := by
  change (cond μ ((realize D) ⁻¹' ((E).coarseTag ⁻¹' {1}))).map
    ((NoisyNativeFiberProduct.commonProjection D P hdR H hBH) ∘ realize D)=_
  rw [←Measure.map_map (NoisyNativeFiberProduct.measurable_commonProjection D P hdR H hBH)
      (measurable_realize D),map_cond_preimage μ (realize D) (measurable_realize D)
        _ ((E).measurable_coarseTag (measurableSet_singleton 1)),
    realize_original_user D P t ht πL π upperBid hupperBid hdR H hBH hfloor (N+1) hrare]
  exact NoisyNativeFiberProduct.common_projection_law D P t ht hdR H hBH πL π
    upperBid hupperBid hfloor N (by simpa only [Nat.cast_add,Nat.cast_one,tailMass] using hrare)

def physicalValue (v : ℝ) (b : Icc (1:ℝ) D.B) (row : Fin N→ Draw) : ℝ :=
  rivalValue Ds (latentTag D P hdR H hBH) (latentBid D P hdR H hBH) μP v b row

lemma measurable_physicalValue (v : ℝ) (b : Icc (1:ℝ) D.B) :
    Measurable (physicalValue D P t ht π hdR H hBH N v b) :=
  measurable_rivalValue Ds _ _ μP (measurable_latentTag D P hdR H hBH)
    (measurable_latentBid D P hdR H hBH) v b

lemma measurable_physicalValue_joint :
    Measurable (fun z : (ℝ×Icc (1:ℝ) D.B)×(Fin N→ Draw) =>
      physicalValue D P t ht π hdR H hBH N z.1.1 z.1.2 z.2) :=
  measurable_rivalValue_joint Ds _ _ μP (measurable_latentTag D P hdR H hBH)
    (measurable_latentBid D P hdR H hBH)

lemma physicalValue_bound (v : ℝ) (b : Icc (1:ℝ) D.B) (row : Fin N→ Draw) :
    |physicalValue D P t ht π hdR H hBH N v b row|≤|v|+2*D.B :=
  rivalValue_bound Ds _ _ μP v b row

include hfloor hrare in
include πL upperBid hupperBid hfloor hrare in
theorem physicalValue_integral (v : ℝ) (b : Icc (1:ℝ) D.B) :
    (∫ row,physicalValue D P t ht π hdR H hBH N v b row
      ∂Measure.pi (fun _ : Fin N => μ))=
      ∑ kind : Fin N→ Fin 4,(CommonList.iid (Ds).categories N).mass kind*
        ∫ row : Fin (D.count kind 1)→ Icc (1:ℝ) D.B,
          regimeValue Ds (D.count kind 1) (min (D.count kind 2) (D.count kind 3)) (max (D.count kind 2) (D.count kind 3)) μP v
            (decide (0< D.count kind 0)) (Fin.cons b row)
          ∂Measure.pi (fun _ : Fin (D.count kind 1) => (ρA : Measure (Icc (1:ℝ) D.B))) :=
  original_rivalValue_integral Ds μ (latentTag D P hdR H hBH) (measurable_latentTag D P hdR H hBH)
    (latentBid D P hdR H hBH) (measurable_latentBid D P hdR H hBH)
    (original_category_ne_zero D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare)
    ρA (original_common_projection D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare) μP
    (original_category_mass D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare) v b

include hfloor hrare in
include πL upperBid hupperBid hfloor hrare in
theorem original_noisy_physicalValue (v : ℝ) (b : Icc (1:ℝ) D.U) :
    (∫ u : unitInterval,∫ row,physicalValue D P t ht π hdR H hBH N v
      (noisyBid (by norm_num : (0:ℝ)<1) D.heps.le (b,u)) row
        ∂Measure.pi (fun _ : Fin N => μ))=
      OrderedFiniteTailNoisyGame.activeExpected Ds N (bidLaws D P t ht π,(v,b)) := by
  have hrho : ρA=noisyBidLaw (by norm_num : (0:ℝ)<1) D.heps.le
      ((Ds).commonLaw (bidLaws D P t ht π)) :=
    NoisyCommonRowLaw.original_common_noisy_law D P t ht π
  have hi (kind : Fin N→ Fin 4) : Integrable (fun u : unitInterval =>
      ∫ row : Fin (D.count kind 1)→ Icc (1:ℝ) D.B,
        regimeValue Ds (D.count kind 1) (min (D.count kind 2) (D.count kind 3)) (max (D.count kind 2) (D.count kind 3)) μP v
          (decide (0< D.count kind 0))
          (Fin.cons (noisyBid (by norm_num : (0:ℝ)<1) D.heps.le (b,u)) row)
        ∂Measure.pi (fun _ : Fin (D.count kind 1) => (ρA : Measure (Icc (1:ℝ) D.B)))) volume := by
    rw [hrho]
    exact ActivePhysicalPayoff.integrable_focal_average Ds _ _ _ μP v _ b
      ((Ds).commonLaw (bidLaws D P t ht π))
  simp_rw [physicalValue_integral D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare]
  have hsum := integral_finsetSum Finset.univ (fun kind _ =>
    (hi kind).const_mul ((CommonList.iid (Ds).categories N).mass kind))
  refine hsum.trans ?_
  unfold OrderedFiniteTailNoisyGame.activeExpected
  refine Finset.sum_congr rfl ?_
  intro kind _
  refine (integral_const_mul _ _).trans ?_
  apply congrArg (fun x : ℝ => (CommonList.iid (Ds).categories N).mass kind*x)
  have htransport := congrArg (fun ρ : ProbabilityMeasure (Icc (1:ℝ) D.B) =>
    ∫ u : unitInterval,∫ row : Fin (D.count kind 1)→Icc (1:ℝ) D.B,
      regimeValue Ds (D.count kind 1) (min (D.count kind 2) (D.count kind 3))
        (max (D.count kind 2) (D.count kind 3)) μP v (decide (0< D.count kind 0))
        (Fin.cons (noisyBid (by norm_num : (0:ℝ)<1) D.heps.le (b,u)) row)
      ∂Measure.pi (fun _ : Fin (D.count kind 1) => (ρ : Measure (Icc (1:ℝ) D.B)))) hrho
  have hsplit := ActivePhysicalPayoff.split_focal_integral Ds
    (D.count kind 1) (min (D.count kind 2) (D.count kind 3))
    (max (D.count kind 2) (D.count kind 3)) μP v (decide (0< D.count kind 0)) b
    ((Ds).commonLaw (bidLaws D P t ht π))
  have hrow := congrArg (fun ν : Measure (Fin (D.count kind 1)→Icc (1:ℝ) (Ds).U) =>
    ∫ row,(Ds).activeRegimeFiber (D.count kind 1) (min (D.count kind 2) (D.count kind 3))
      (max (D.count kind 2) (D.count kind 3)) (decide (0< D.count kind 0))
      ((v,b,μP),row) ∂ν)
    (rowLaw_eq_pi (D.count kind 1) ((Ds).commonLaw (bidLaws D P t ht π))).symm
  exact htransport.trans (hsplit.trans hrow)

include hfloor hrare in
include t ht πL π upperBid hupperBid hfloor hrare in
theorem ae_original_focal_distinct (b : Icc (1:ℝ) D.B) :
    ∀ᵐ row ∂Measure.pi (fun _ : Fin N => μ),
      ∀ i j : Fin (D.count (tags (latentTag D P hdR H hBH) row) 1+1),i≠j→
        (focalRow D (tags (latentTag D P hdR H hBH) row)
          (latentBid D P hdR H hBH) b row i:ℝ)≠
        (focalRow D (tags (latentTag D P hdR H hBH) row)
          (latentBid D P hdR H hBH) b row j:ℝ) := by
  apply ae_of_all_category_fibers μ (latentTag D P hdR H hBH)
    (measurable_latentTag D P hdR H hBH)
  intro kind
  have hp : MeasurePreserving (commonRow D kind (latentBid D P hdR H hBH))
      (Measure.pi (fun i => cond μ (latentTag D P hdR H hBH ⁻¹' {kind i})))
      (Measure.pi (fun _ : Fin (D.count kind 1) => (ρA : Measure (Icc (1:ℝ) D.B)))) :=
    ⟨measurable_commonRow D kind (latentBid D P hdR H hBH) (measurable_latentBid D P hdR H hBH),
      commonRow_law D μ (latentTag D P hdR H hBH)
        (latentBid D P hdR H hBH) (measurable_latentBid D P hdR H hBH)
        (original_category_ne_zero D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare)
        ρA (original_common_projection D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare) kind⟩
  have hd : ∀ᵐ r : Fin (D.count kind 1)→Icc (1:ℝ) D.B
      ∂Measure.pi (fun _ : Fin (D.count kind 1) => (ρA : Measure (Icc (1:ℝ) D.B))),
      ∀ i j : Fin (D.count kind 1+1),i≠j→
        ((Fin.cons b r : Fin (D.count kind 1+1)→Icc (1:ℝ) D.B) i:ℝ)≠
        ((Fin.cons b r : Fin (D.count kind 1+1)→Icc (1:ℝ) D.B) j:ℝ) := by
    change ∀ᵐ r : Fin (D.count kind 1)→Icc (1:ℝ) D.B
      ∂Measure.pi (fun _ : Fin (D.count kind 1) =>
        ((bidMarginal (activePhysical D P t ht π).1) : Measure (Icc (1:ℝ) D.B))),_
    rw [NoisyCommonRowLaw.original_common_noisy_law D P t ht π]
    have hh : ∀ᵐ r : Fin (D.count kind 1)→Icc (1:ℝ) D.B
        ∂Measure.pi (fun _ : Fin (D.count kind 1) =>
          ProbabilityMeasure.toMeasure (show ProbabilityMeasure (Icc (1:ℝ) D.B) from
            noisyBidLaw (by norm_num : (0:ℝ)<1) D.heps.le
              ((Ds).commonLaw (bidLaws D P t ht π)))),
        ∀ i j : Fin (D.count kind 1+1),i≠j→
          (Fin.cons (b:ℝ) (fun k => (r k:ℝ)) : Fin (D.count kind 1+1)→ℝ) i≠
          (Fin.cons (b:ℝ) (fun k => (r k:ℝ)) : Fin (D.count kind 1+1)→ℝ) j :=
      OriginalNoiseProduct.ae_cons_physicalRow_distinct (by norm_num : (0:ℝ)<1) D.heps
        (D.count kind 1) ((Ds).commonLaw (bidLaws D P t ht π)) b
    filter_upwards [hh] with r hr
    intro i j hij
    have hc (k : Fin (D.count kind 1+1)) :=
      congrFun (Fin.comp_cons (fun x : Icc (1:ℝ) D.B => (x:ℝ)) b r) k
    exact (by simpa only [Function.comp_apply] using hc i) ▸
      ((by simpa only [Function.comp_apply] using hc j) ▸ hr i j hij)
  have ht' := ae_tags_conditional μ (latentTag D P hdR H hBH)
    (measurable_latentTag D P hdR H hBH)
    (original_category_ne_zero D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare) kind
  filter_upwards [ht',hp.quasiMeasurePreserving.ae hd] with row hrow hd
  subst kind
  simpa only [focalRow] using hd

include hfloor hrare in
include t ht πL π upperBid hupperBid hfloor hrare in
theorem ae_original_carrier_distinct (J : Set Draw) :
    ∀ᵐ z : Draw×(Fin N→Draw) ∂((μ).restrict J).prod (Measure.pi (fun _ : Fin N => μ)),
      ∀ i j : Fin (D.count (tags (latentTag D P hdR H hBH) z.2) 1+1),i≠j→
        (focalRow D (tags (latentTag D P hdR H hBH) z.2)
          (latentBid D P hdR H hBH) (latentBid D P hdR H hBH z.1) z.2 i:ℝ)≠
        (focalRow D (tags (latentTag D P hdR H hBH) z.2)
          (latentBid D P hdR H hBH) (latentBid D P hdR H hBH z.1) z.2 j:ℝ) := by
  let Q (kind : Fin N→Fin 4) (z : Draw×(Fin N→Draw)) : Prop :=
    ∀ i j : Fin (D.count kind 1+1),i≠j→
      (focalRow D kind (latentBid D P hdR H hBH) (latentBid D P hdR H hBH z.1) z.2 i:ℝ)≠
      (focalRow D kind (latentBid D P hdR H hBH) (latentBid D P hdR H hBH z.1) z.2 j:ℝ)
  have hQ (kind : Fin N→Fin 4) : MeasurableSet {z | Q kind z} := by
    have hf : Measurable (fun z : Draw×(Fin N→Draw) =>
        focalRow D kind (latentBid D P hdR H hBH) (latentBid D P hdR H hBH z.1) z.2) :=
      (measurable_focalRow D kind (latentBid D P hdR H hBH) (measurable_latentBid D P hdR H hBH)).comp
        (((measurable_latentBid D P hdR H hBH).comp measurable_fst).prodMk measurable_snd)
    simp only [Q,Set.setOf_forall]
    exact MeasurableSet.iInter (fun i => MeasurableSet.iInter (fun j =>
      MeasurableSet.iInter (fun _ => (measurableSet_eq_fun
        (((measurable_pi_apply i).comp hf).subtype_val)
        (((measurable_pi_apply j).comp hf).subtype_val)).compl)))
  have hm : MeasurableSet {z : Draw×(Fin N→Draw) |
      Q (tags (latentTag D P hdR H hBH) z.2) z} := by
    have he : {z : Draw×(Fin N→Draw) | Q (tags (latentTag D P hdR H hBH) z.2) z}=
        {z | ∀ kind : Fin N→Fin 4,tags (latentTag D P hdR H hBH) z.2=kind→Q kind z} := by
      ext z
      constructor
      · intro hz kind hk
        change Q (tags (latentTag D P hdR H hBH) z.2) z at hz
        simpa only [←hk] using hz
      · intro hz
        exact hz _ rfl
    rw [he,Set.setOf_forall]
    exact MeasurableSet.iInter (fun kind => (measurableSet_eq_fun
      ((measurable_tags (latentTag D P hdR H hBH) (measurable_latentTag D P hdR H hBH)).comp measurable_snd)
      measurable_const).imp (hQ kind))
  apply (Measure.ae_prod_iff_ae_ae hm).mpr
  exact ae_of_all _ fun x =>
    ae_original_focal_distinct D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare
      (latentBid D P hdR H hBH x)

end FCAppendix.Affine.Tail04.OrderedAtomActiveLaw
