import FCAppendix.Affine.Tail04.OrderedZeroUnusedOriginal
import FCAppendix.Affine.Tail04.SourceUnusedConstants

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedSourceNativeUnusedCount
open MeasureTheory ProbabilityTheory Set Filter Topology Classical Game Bayes
open Existence.Distributional OriginalValues OriginalPopulation
open FiniteTailNoisyGame SourceTailNoisyFixedPoint OrderedNativeZeroNoiseSource OrderedZeroNativeBindings
open OriginalActiveCompression OrderedZeroCommonMenuCount OrderedZeroSourceUnusedPublic
open MenuError SourceMenuPopulation SourceMenuError SourceMomentRectangle
open UnusedFiniteCountError UnusedRowAverage
open scoped BigOperators

variable (D : Data) (P : ValueParameters) (t : ℝ) (ht : P.M< t)
  (πL : Law (A:=LowBody.LowValue P.d0) P.originalLowLaw)
  (π : JointProfile D P t ht) (upperBid : ℝ→ℝ) (hupperBid : Measurable upperBid)
  (hdR : P.d0< D.R) (H : ℝ) (hUH : D.U< H)
  (hfloor : ∀v,t< v→ H≤ upperBid v) (N : ℕ)
  (hrare : (1-D.ξ)*D.U+D.ξ*D.U*((N+1:ℕ)*
    (tailMass P t/(partialMass+tailMass P t)))≤ D.R)

variable (cats : FiniteLaw (Fin 4))
  (L : LowBody.ActualAtomlessLowLimit N P.d0 D.ξ D.c cats P.originalLowLaw)
  (hL : πL=L.joint)
  (hcap : D.c=iidCapacity (99/200) N) (hN : 0< N)
  (hF : D.F=(Central.B D.ξ)) (hflags : ∀reg,D.e0 reg=baseFlag P reg)
  (hξh : D.ξ<1/2) (hR : D.R=Central.R D.ξ) (huB : 1+D.u< (Central.B D.ξ))
  (hRp : D.Up≤ Central.R D.ξ+D.ξ/1000)
  (hsmall : relativeError P.zeta D.u (Central.B D.ξ)≤ D.ξ/1000)
  (hmSmall : upperMass P t≤ Central.mixedR (P.theta^2)/1000)
  (hwγ : D.width≤ γ D.ξ)
  (hsize : ∀reg,4*D.ξ/((N:ℝ)*centerMoment P reg)≤ γ D.ξ)
  (hbulk : 1≤ P.bulkWeight*(N:ℝ)/2)

include cats L hL hcap hN hF hflags hξh hR huB hRp hsmall hmSmall hwγ hsize hbulk in
theorem original_count_error (i : Fin (N+1)) (y : ℝ)
    (hy : y∈Icc (0:ℝ) (Central.B D.ξ)) (htag : (regions D P hdR H hUH).localTag (some y)=1)
    (hout : y∉Icc (1:ℝ) D.U) (f : Fin 3→ℝ) :
    |((problem (game D P t ht hdR H hUH πL π upperBid hupperBid hfloor (N+1) hrare) i).outcome (RawRoutes.action y hy.1 2)).expect f-
      (canonicalMixture (publicData D P t ht hdR H hUH πL π upperBid hupperBid hfloor) (OrderedZeroSourceCommonMenuError.lambda D P t ht πL π upperBid hupperBid hdR H hUH hfloor N hrare) y).expect f|≤
        MenuError.oscillation f*SourceUnusedConstants.rate P D.ξ D.u N := by
  let target:=canonicalMixture (publicData D P t ht hdR H hUH πL π upperBid hupperBid hfloor) (OrderedZeroSourceCommonMenuError.lambda D P t ht πL π upperBid hupperBid hdR H hUH hfloor N hrare) y
  let g : (Fin N→ UserDraw 2)→ℝ:=fun r=>
    |(OrderedZeroSourceUnusedPublic.count D P t ht πL π upperBid hupperBid hdR H hUH hfloor N r y).expect f-
        target.expect f|+
      4*MenuError.oscillation f*bad D P t ht πL π upperBid hupperBid hdR H hUH hfloor N r
  let K0:=SourceUnusedConstants.regimeCoefficient P D.ξ false
  let K1:=SourceUnusedConstants.regimeCoefficient P D.ξ true
  let J:=SourceUnusedConstants.integerCoefficient P
  let C:=SourceUnusedConstants.crossingCoefficient P (Central.B D.ξ) D.u D.ξ
  let B:=badBulk D P N
  let ind : (Fin N→ UserDraw 2)→ℝ:=fun r=> if r∈B then 1 else 0
  let rem : (Fin N→ UserDraw 2)→ℝ:=fun r=>
    MenuError.oscillation f*(K0*(empirical D P t ht πL π upperBid hupperBid hdR H hUH hfloor N hrare) false r+K1*(empirical D P t ht πL π upperBid hupperBid hdR H hUH hfloor N hrare) true r+J/(N:ℝ)+2*C/Real.sqrt N+6*ind r)
  have hE (reg : Bool) : Integrable ((empirical D P t ht πL π upperBid hupperBid hdR H hUH hfloor N hrare) reg) (Measure.pi (fun _ : Fin N=> (userLaw (game D P t ht hdR H hUH πL π upperBid hupperBid hfloor (N+1) hrare)))) :=
    UnusedEmpiricalGuard.integrable_averageError (userLaw (game D P t ht hdR H hUH πL π upperBid hupperBid hfloor (N+1) hrare)) N hN (tagFlag ((regions D P hdR H hUH).coarseTag) 1) (tagFlag ((regions D P hdR H hUH).coarseTag) 2) (tagFlag ((regions D P hdR H hUH).coarseTag) 3)
      (measurable_tagFlag ((regions D P hdR H hUH).coarseTag) (regions D P hdR H hUH).measurable_coarseTag 1)
      (measurable_tagFlag ((regions D P hdR H hUH).coarseTag) (regions D P hdR H hUH).measurable_coarseTag 2)
      (measurable_tagFlag ((regions D P hdR H hUH).coarseTag) (regions D P hdR H hUH).measurable_coarseTag 3)
      (flag (installOriginal D P t ht) (ZeroNativeFiberProduct.commonProjection D P hdR H hUH) reg) (measurable_flag (installOriginal D P t ht) (ZeroNativeFiberProduct.commonProjection D P hdR H hUH)
        (ZeroNativeFiberProduct.measurable_commonProjection D P hdR H hUH) reg)
      (fun x=>((ZeroNativeFiberProduct.commonProjection D P hdR H hUH) x:ℝ)) (ZeroNativeFiberProduct.measurable_commonProjection D P hdR H hUH).subtype_val
  have hEi (reg : Bool) : (∫r,(empirical D P t ht πL π upperBid hupperBid hdR H hUH hfloor N hrare) reg r ∂(Measure.pi (fun _ : Fin N=> (userLaw (game D P t ht hdR H hUH πL π upperBid hupperBid hfloor (N+1) hrare)))))≤5/Real.sqrt N+5/(N:ℝ) :=
    UnusedEmpiricalGuard.averageError_L1 (userLaw (game D P t ht hdR H hUH πL π upperBid hupperBid hfloor (N+1) hrare)) N hN (tagFlag ((regions D P hdR H hUH).coarseTag) 1) (tagFlag ((regions D P hdR H hUH).coarseTag) 2) (tagFlag ((regions D P hdR H hUH).coarseTag) 3)
      (measurable_tagFlag ((regions D P hdR H hUH).coarseTag) (regions D P hdR H hUH).measurable_coarseTag 1)
      (measurable_tagFlag ((regions D P hdR H hUH).coarseTag) (regions D P hdR H hUH).measurable_coarseTag 2)
      (measurable_tagFlag ((regions D P hdR H hUH).coarseTag) (regions D P hdR H hUH).measurable_coarseTag 3)
      (flag (installOriginal D P t ht) (ZeroNativeFiberProduct.commonProjection D P hdR H hUH) reg) (measurable_flag (installOriginal D P t ht) (ZeroNativeFiberProduct.commonProjection D P hdR H hUH)
        (ZeroNativeFiberProduct.measurable_commonProjection D P hdR H hUH) reg)
      (fun x=>((ZeroNativeFiberProduct.commonProjection D P hdR H hUH) x:ℝ)) (ZeroNativeFiberProduct.measurable_commonProjection D P hdR H hUH).subtype_val
  have hB : MeasurableSet B:=measurable_badBulk D P N
  have hi : Integrable ind (Measure.pi (fun _ : Fin N=> (userLaw (game D P t ht hdR H hUH πL π upperBid hupperBid hfloor (N+1) hrare)))):=Integrable.of_bound
    (Measurable.ite hB measurable_const measurable_const).aestronglyMeasurable 1
      (ae_of_all _ fun r=> by dsimp only [ind];split_ifs <;> norm_num)
  have hind : (∫r,ind r ∂(Measure.pi (fun _ : Fin N=> (userLaw (game D P t ht hdR H hUH πL π upperBid hupperBid hfloor (N+1) hrare)))))=(Measure.pi (fun _ : Fin N=> (userLaw (game D P t ht hdR H hUH πL π upperBid hupperBid hfloor (N+1) hrare)))).real B := by
    simpa only [ind,Set.indicator,Pi.one_apply] using! integral_indicator_one (μ:=(Measure.pi (fun _ : Fin N=> (userLaw (game D P t ht hdR H hUH πL π upperBid hupperBid hfloor (N+1) hrare))))) hB
  have hrem : Integrable rem (Measure.pi (fun _ : Fin N=> (userLaw (game D P t ht hdR H hUH πL π upperBid hupperBid hfloor (N+1) hrare)))):=
    (((((hE false).const_mul K0).add ((hE true).const_mul K1)).add
      (integrable_const _)).add (integrable_const _)).add (hi.const_mul 6) |>.const_mul _
  have hg : Integrable g (Measure.pi (fun _ : Fin N=> (userLaw (game D P t ht hdR H hUH πL π upperBid hupperBid hfloor (N+1) hrare)))) := by
    let obs : (kind : Fin N→ Fin 4)→(Fin ((installOriginal D P t ht).count kind 1)→ Icc (1:ℝ) D.U)→ℝ:=
      fun kind=> totalError (publicData D P t ht hdR H hUH πL π upperBid hupperBid hfloor) ((installOriginal D P t ht).count kind 1) (min ((installOriginal D P t ht).count kind 2) ((installOriginal D P t ht).count kind 3),max ((installOriginal D P t ht).count kind 2) ((installOriginal D P t ht).count kind 3))
        D.U (Central.B D.ξ) D.R D.Up D.width (γ D.ξ) (D.ξ/4) y target f
    have hh:=ZeroOriginalRowCompression.integrable_rowObservable (installOriginal D P t ht) (Measure.pi (fun _ : Fin N=> (userLaw (game D P t ht hdR H hUH πL π upperBid hupperBid hfloor (N+1) hrare)))) ((regions D P hdR H hUH).coarseTag) (regions D P hdR H hUH).measurable_coarseTag
      (ZeroNativeFiberProduct.commonProjection D P hdR H hUH) (ZeroNativeFiberProduct.measurable_commonProjection D P hdR H hUH)
      obs (fun kind=> measurable_totalError (publicData D P t ht hdR H hUH πL π upperBid hupperBid hfloor) _ _ _ _ _ _ _ _ _ _ target f) (6*MenuError.oscillation f)
      (fun kind row=> by
        have hb : obs kind row∈Icc (0:ℝ) (6*MenuError.oscillation f) := totalError_bounds (publicData D P t ht hdR H hUH πL π upperBid hupperBid hfloor) _ _ _ _ _ _ _ _ _ _ target f row
        rw [Real.norm_eq_abs,abs_of_nonneg hb.1]
        exact hb.2)
    exact hh
  have hpoint (r : Fin N→ UserDraw 2) : g r≤ rem r :=
    row_total_error D P t ht πL π upperBid hupperBid hdR H hUH hfloor N hrare
      hcap hN hF hflags hξh hR huB hRp hsmall hmSmall hwγ hsize hbulk r y hy f
  have hint : (∫r,g r ∂(Measure.pi (fun _ : Fin N=> (userLaw (game D P t ht hdR H hUH πL π upperBid hupperBid hfloor (N+1) hrare)))))≤∫r,rem r ∂(Measure.pi (fun _ : Fin N=> (userLaw (game D P t ht hdR H hUH πL π upperBid hupperBid hfloor (N+1) hrare)))) := integral_mono hg hrem hpoint
  have hremI : (∫r,rem r ∂(Measure.pi (fun _ : Fin N=> (userLaw (game D P t ht hdR H hUH πL π upperBid hupperBid hfloor (N+1) hrare)))))=MenuError.oscillation f*(K0*(∫r,(empirical D P t ht πL π upperBid hupperBid hdR H hUH hfloor N hrare) false r ∂(Measure.pi (fun _ : Fin N=> (userLaw (game D P t ht hdR H hUH πL π upperBid hupperBid hfloor (N+1) hrare)))))+K1*(∫r,(empirical D P t ht πL π upperBid hupperBid hdR H hUH hfloor N hrare) true r ∂(Measure.pi (fun _ : Fin N=> (userLaw (game D P t ht hdR H hUH πL π upperBid hupperBid hfloor (N+1) hrare)))))+
      J/(N:ℝ)+2*C/Real.sqrt N+6*(Measure.pi (fun _ : Fin N=> (userLaw (game D P t ht hdR H hUH πL π upperBid hupperBid hfloor (N+1) hrare)))).real B) := by
    unfold rem
    erw [integral_const_mul,
      integral_add (((((hE false).const_mul K0).add ((hE true).const_mul K1)).add
        (integrable_const _)).add (integrable_const _)) (hi.const_mul 6),
      integral_add ((((hE false).const_mul K0).add ((hE true).const_mul K1)).add
        (integrable_const _)) (integrable_const _),
      integral_add (((hE false).const_mul K0).add ((hE true).const_mul K1)) (integrable_const _),
      integral_add ((hE false).const_mul K0) ((hE true).const_mul K1)]
    simp only [integral_const_mul,integral_const,probReal_univ,one_smul,hind]
  have hb:=SourceZeroBulkEvent.original_iid_bulk_lower_tail D P t ht πL π upperBid hupperBid
    hdR H hUH hfloor N hrare hN
  have hn:=ZeroSourceCommonMoments.source_noLow D P t ht πL π upperBid hupperBid
    hdR H hUH hfloor N hrare hN
  have hnativ:=OrderedZeroUnusedOriginal.source_original_error D P t ht hdR H hUH πL π
    upperBid hupperBid hfloor N hrare cats L hL i y hy.1 htag hout target f
  change (Measure.pi (fun _ : Fin N=>userLaw (game D P t ht hdR H hUH πL π upperBid hupperBid hfloor (N+1) hrare))).real B≤_ at hb
  change (Measure.pi (fun _ : Fin N=>userLaw (game D P t ht hdR H hUH πL π upperBid hupperBid hfloor (N+1) hrare))).real
    {r | (installOriginal D P t ht).count (tags (regions D P hdR H hUH).coarseTag r) 0=0}≤_ at hn
  have hK0 : 0≤ K0:=SourceUnusedConstants.regimeCoefficient_nonneg P D.hξ false
  have hK1 : 0≤ K1:=SourceUnusedConstants.regimeCoefficient_nonneg P D.hξ true
  have hh0:=mul_le_mul_of_nonneg_left (hEi false) hK0
  have hh1:=mul_le_mul_of_nonneg_left (hEi true) hK1
  have hho:=oscillation_nonneg f
  have hhb:=mul_le_mul_of_nonneg_left hb (by positivity : 0≤6*MenuError.oscillation f)
  have hhn:=mul_le_mul_of_nonneg_left hn (by positivity : 0≤2*MenuError.oscillation f)
  have hhe:=mul_le_mul_of_nonneg_left (add_le_add hh0 hh1) hho
  rw [hremI] at hint
  change |_ - _|≤_
  dsimp only [g,target,rem,B,K0,K1,J,C] at *
  unfold SourceUnusedConstants.rate SourceUnusedConstants.coefficient
  simp only [div_eq_mul_inv] at hnativ hint hhe hhb hhn ⊢
  nlinarith only [hnativ,hint,hhe,hhb,hhn]

end FCAppendix.Affine.Tail04.OrderedSourceNativeUnusedCount
