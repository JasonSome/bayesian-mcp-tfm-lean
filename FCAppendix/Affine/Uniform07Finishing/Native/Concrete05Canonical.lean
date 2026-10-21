import FCAppendix.Affine.Uniform07Finishing.Native.Concrete05Capped
import FCAppendix.Affine.Uniform07Finishing.Native.SourceCanonicalPhysical
import FCAppendix.Affine.Uniform07Finishing.Crossover.Received05CanonicalBridge

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing.Concrete05
open MeasureTheory ProbabilityTheory Game Bayes Set Classical Filter Topology
open FCAppendix.Affine UniformFinite LowBody StrictNative Weighted
open Crossover.Physical
open scoped BigOperators
variable {row : Uniform07.Row} {m : ℕ} [Nonempty (Fin m)]

local instance : NeZero m := ⟨by
  have hi := (Classical.choice (inferInstance : Nonempty (Fin m))).isLt
  omega⟩

def nativeCanonicalEvent (E : UniformFinite.ExactRestrictedLaw row m)
    (hc : 1≤ Uniform07.capacity m) (R : ℝ) (i : Fin m) :
    Crossover.Physical.CanonicalEvent (nativeGame E hc R) where
  event b := {ω | sourceCanonicalSelected (Uniform07.xi row) E.law.multiplier
    (Early.demandRatio row) (Early.bidCap row) (Uniform07.cutoff row/2)
    (Uniform07.capacity m) (sourceSeedMeasure row m hc R (lowerJoint E))
    (literalSourceAlpha row E.law.multiplier E.law.rejectionRoot
      (10*UniformFinite.Source.commonGuardMargin row) (UniformFinite.Source.commonGuardMargin row))
    (focalInputContext R i (Crossover.Physical.two b) (ω.1.1,ω.2))}
  measurable b := (measurableSet_sourceCanonicalSelected (Uniform07.xi row) E.law.multiplier
    (Early.demandRatio row) (Early.bidCap row) (Uniform07.cutoff row/2)
    (Uniform07.xi_pos row) (source_guard_multiplier_positive row (multiplier_lower E))
    (Uniform07.capacity m) (sourceSeedMeasure row m hc R (lowerJoint E))
    (literalSourceAlpha row E.law.multiplier E.law.rejectionRoot
      (10*UniformFinite.Source.commonGuardMargin row) (UniformFinite.Source.commonGuardMargin row))
    (measurable_literalSourceAlpha row (multiplier_lower E) E.law.rejectionRoot
      (10*UniformFinite.Source.commonGuardMargin row) (UniformFinite.Source.commonGuardMargin row))).preimage
    ((measurable_focalInputContext R i (Crossover.Physical.two b)).comp
      (measurable_fst.fst.prodMk measurable_snd))

def nativeCanonicalMoment (E : UniformFinite.ExactRestrictedLaw row m)
    (hc : 1≤ Uniform07.capacity m) (R : ℝ) (i : Fin m) (a : JointAction 2)
    (q : Fin 3→ℝ) : ℝ :=
  ∫ω,sourceCanonicalSampleTest (nativeGame E hc R) R (Uniform07.xi row) E.law.multiplier
    (Early.demandRatio row) (Early.bidCap row) (Uniform07.cutoff row/2)
    (sourceSeedMeasure row m hc R (lowerJoint E))
    (literalSourceAlpha row E.law.multiplier E.law.rejectionRoot
      (10*UniformFinite.Source.commonGuardMargin row) (UniformFinite.Source.commonGuardMargin row))
    i a q ω ∂sampleLaw (nativeGame E hc R)

theorem nativeCanonicalMoment_eq_event (E : UniformFinite.ExactRestrictedLaw row m)
    (hc : 1≤ Uniform07.capacity m) (R : ℝ) (i : Fin m) (b : ℝ) (q : Fin 3→ℝ) :
    nativeCanonicalMoment E hc R i (Crossover.Physical.two b) q=
      ∫ω in (nativeCanonicalEvent E hc R i).event b,
        q (focalCount (nativeGame E hc R) i (Crossover.Physical.two b) ω)
        ∂sampleLaw (nativeGame E hc R) := by
  rw [←integral_indicator ((nativeCanonicalEvent E hc R i).measurable b)]
  rfl

def nativeCanonicalNumericMoment (row : Uniform07.Row) (G : Uniform05.RestrictedLaw row)
    (i : Fin m) (own : ℝ) (q : Fin 3→ℝ)
    (z : Fin m→ UniformFinite.NumericObservation row) : ℝ :=
  let X := UniformFinite.Late.ExceptionalProfile.numericContext row i own z
  (if budget (Uniform07.capacity m) 0 X=budget (Uniform07.capacity m) 1 X then
    privateCountMoment (Uniform07.xi row) (Uniform07.xi_pos row) (source_xi_lt_one row)
      (Uniform07.capacity m) X none i q else 0)+
    if numericRivalHasSeed row i z then
      finiteCanonicalPart (Uniform07.xi row) (Uniform07.xi_pos row) (source_xi_lt_one row)
        G.multiplier (Early.demandRatio row) (Early.bidCap row) (Uniform07.capacity m)
        (literalSourceAlpha row G.multiplier G.rejectionRoot
          (10*UniformFinite.Source.commonGuardMargin row) (UniformFinite.Source.commonGuardMargin row)) X i q
    else 0

theorem measurable_nativeCanonicalNumericMoment (row : Uniform07.Row)
    (G : Uniform05.RestrictedLaw row) (i : Fin m) (own : ℝ) (q : Fin 3→ℝ) :
    Measurable (nativeCanonicalNumericMoment row G i own q) := by
  have hX := UniformFinite.Late.ExceptionalProfile.measurable_numericContext row i own
  have hΛ : (54/100:ℝ)*Uniform07.cutoff row< G.multiplier := by
    simpa only [Uniform05.t_eq_canonical] using G.multiplier_guards.1
  exact (Measurable.ite
    (measurableSet_eq_fun ((measurable_budget (Uniform07.capacity m) 0).comp hX)
      ((measurable_budget (Uniform07.capacity m) 1).comp hX))
    ((measurable_privateCountMoment (Uniform07.xi row) (Uniform07.xi_pos row)
      (source_xi_lt_one row) (Uniform07.capacity m) i q).comp
      (hX.prodMk measurable_const)) measurable_const).add
    (Measurable.ite (measurableSet_numericRivalHasSeed row i)
      ((measurable_finiteCanonicalPart (Uniform07.xi row) (Uniform07.xi_pos row)
        (source_xi_lt_one row) G.multiplier (Early.demandRatio row) (Early.bidCap row)
        (source_guard_multiplier_positive row hΛ) (Uniform07.capacity m)
        (literalSourceAlpha row G.multiplier G.rejectionRoot
          (10*UniformFinite.Source.commonGuardMargin row) (UniformFinite.Source.commonGuardMargin row))
        (measurable_literalSourceAlpha row hΛ G.rejectionRoot
          (10*UniformFinite.Source.commonGuardMargin row) (UniformFinite.Source.commonGuardMargin row))
        i q).comp hX) measurable_const)

theorem abs_nativeCanonicalNumericMoment_le (row : Uniform07.Row)
    (G : Uniform05.RestrictedLaw row) (i : Fin m) (own : ℝ) (q : Fin 3→ℝ)
    (z : Fin m→ UniformFinite.NumericObservation row) :
    |nativeCanonicalNumericMoment row G i own q z|≤ 2*∑k : Fin 3,|q k| := by
  let X := UniformFinite.Late.ExceptionalProfile.numericContext row i own z
  have hB := abs_privateCountMoment_le (Uniform07.xi row) (Uniform07.xi_pos row)
    (source_xi_lt_one row) (Uniform07.capacity m) X none i q
  have hC := abs_finiteCanonicalPart_le (Uniform07.xi row) (Uniform07.xi_pos row)
    (source_xi_lt_one row) G.multiplier (Early.demandRatio row) (Early.bidCap row)
    (Uniform07.capacity m) (literalSourceAlpha row G.multiplier G.rejectionRoot
      (10*UniformFinite.Source.commonGuardMargin row) (UniformFinite.Source.commonGuardMargin row)) X i q
  have hq : 0≤∑k : Fin 3,|q k| := Finset.sum_nonneg (fun _ _=>abs_nonneg _)
  have hB' : |if budget (Uniform07.capacity m) 0 X=budget (Uniform07.capacity m) 1 X then
      privateCountMoment (Uniform07.xi row) (Uniform07.xi_pos row) (source_xi_lt_one row)
        (Uniform07.capacity m) X none i q else 0|≤∑k : Fin 3,|q k| := by
    split_ifs
    · exact hB
    · simpa only [abs_zero] using hq
  have hC' : |if numericRivalHasSeed row i z then
      finiteCanonicalPart (Uniform07.xi row) (Uniform07.xi_pos row) (source_xi_lt_one row)
        G.multiplier (Early.demandRatio row) (Early.bidCap row) (Uniform07.capacity m)
        (literalSourceAlpha row G.multiplier G.rejectionRoot
          (10*UniformFinite.Source.commonGuardMargin row) (UniformFinite.Source.commonGuardMargin row))
        X i q else 0|≤∑k : Fin 3,|q k| := by
    split_ifs
    · exact hC
    · simpa only [abs_zero] using hq
  exact (abs_add_le _ _).trans (by linarith)

theorem decoded_finiteCanonicalPart (row : Uniform07.Row) (G : Uniform05.RestrictedLaw row)
    [NeZero m] (hm : 0< m) (X : ClassifiedContext m)
    (hX : UniformFinite.NativeContext.Valid X) (h0 : NonnegativeList X.1)
    (hU : ∀k,entryBid (X.1 k)≤ Early.bidCap row)
    (he : budget (Uniform07.capacity m) 0 X≠budget (Uniform07.capacity m) 1 X)
    (i : Fin m) (q : Fin 3→ℝ) :
    finiteCanonicalPart (Uniform07.xi row) (Uniform07.xi_pos row) (source_xi_lt_one row)
      G.multiplier (Early.demandRatio row) (Early.bidCap row) (Uniform07.capacity m)
      (literalSourceAlpha row G.multiplier G.rejectionRoot
        (10*UniformFinite.Source.commonGuardMargin row) (UniformFinite.Source.commonGuardMargin row)) X i q=
      UniformFinite.Source.rawAlpha row G (UniformFinite.NativeContext.decode X)
        (fun k=>entryBid (X.1 k))*
      (UniformFinite.canonicalLaw row G (UniformFinite.NativeContext.decode X)
        (fun k=>entryBid (X.1 k))).expect (fun P=>q (UniformFinite.pairCount i P)) := by
  let α := literalSourceAlpha (m:=m) row G.multiplier G.rejectionRoot
    (10*UniformFinite.Source.commonGuardMargin row) (UniformFinite.Source.commonGuardMargin row)
  have hαeq : UniformFinite.Source.rawAlpha row G (UniformFinite.NativeContext.decode X)
      (fun k=>entryBid (X.1 k))=(α X:ℝ) :=
    rawAlpha_eq_sourceGuardAlpha row G hm X hX hU
  have hcorr := decoded_raw_count_correction row G hm X hX h0 hU i q
  by_cases ha : 0<(α X:ℝ)
  · have hW := sourceGuardAlpha_outer (Uniform07.capacity m) hm
      (UniformFinite.Source.common_guard_margin row) X ha 2
    have hεm : 0< UniformFinite.Source.commonGuardMargin row*(m:ℝ) :=
      mul_pos (UniformFinite.Source.common_guard_margin row) (by exact_mod_cast hm)
    have hg : (exceptionalSet (Early.bidCap row) X.1).card≤ 1 ∧
      ((max (budget (Uniform07.capacity m) 0 X) (budget (Uniform07.capacity m) 1 X)-
        commonBudget (Uniform07.capacity m) X : ℕ):ℝ)<
        WeightedSampling.totalWeight (sourceWeights (Uniform07.xi row) G.multiplier
          (Early.demandRatio row) (Early.bidCap row) X.1) := by
      constructor
      · rw [capped_exceptionalSet_empty row X hU]; simp
      · change UniformFinite.Source.commonGuardMargin row*(m:ℝ)<
          WeightedSampling.totalWeight (sourceWeights (Uniform07.xi row) G.multiplier
            (Early.demandRatio row) (Early.bidCap row) X.1)-
          ((max (budget (Uniform07.capacity m) 0 X) (budget (Uniform07.capacity m) 1 X)-
            commonBudget (Uniform07.capacity m) X : ℕ):ℝ) at hW
        linarith
    rw [finiteCanonicalPart_formula,if_neg he,if_pos hg]
    simp only [finitePathCountCorrection,if_pos hg] at hcorr
    rw [hαeq] at hcorr ⊢
    change (α X:ℝ)*_=(α X:ℝ)*_ at hcorr
    change (α X:ℝ)*_=_
    linarith only [hcorr]
  · have hz : (α X:ℝ)=0 := le_antisymm (le_of_not_gt ha) (α X).property.1
    rw [hαeq,hz,zero_mul,finiteCanonicalPart_formula,if_neg he]
    dsimp only
    change (if _ then (α X:ℝ)*_ else 0)=0
    split_ifs <;> simp only [hz,zero_mul]

theorem numeric_canonical_moment_eq05 (row : Uniform07.Row)
    (G : Uniform05.RestrictedLaw row) [NeZero m] (hm : 0< m)
    (i : Fin m) (own : Uniform05.Bid row) (z : Fin m→ UniformFinite.NumericObservation row)
    (q : Fin 3→ℝ) (hq : q 0=0) :
    nativeCanonicalNumericMoment row G i own q z=
      Crossover.Received06.rowCanonicalMoment05 row G
        (UniformFinite.Late.ExceptionalProfile.numericRow row i z)
        (UniformFinite.Late.ExceptionalProfile.numericBids row i own z) i q := by
  let X := UniformFinite.Late.ExceptionalProfile.numericContext row i own z
  obtain ⟨hX,h0,hU,hi⟩ := numeric_context_properties row i own z
  have hD := UniformFinite.Late.ExceptionalProfile.decode_rowContext
    (UniformFinite.Late.ExceptionalProfile.numericRow row i z)
    (UniformFinite.Late.ExceptionalProfile.numericBids row i own z)
  have hentries := numeric_context_entries row i own z
  have heq : (UniformFinite.Source.residual (UniformFinite.NativeContext.decode X) 0=
      UniformFinite.Source.residual (UniformFinite.NativeContext.decode X) 1) ↔
      budget (Uniform07.capacity m) 0 X=budget (Uniform07.capacity m) 1 X := by
    rw [decoded_residual X hX,decoded_residual X hX]
  rw [show UniformFinite.Late.ExceptionalProfile.numericRow row i z=
      UniformFinite.NativeContext.decode X from hD.symm,
    show UniformFinite.Late.ExceptionalProfile.numericBids row i own z=
      (fun k=>entryBid (X.1 k)) from hentries.symm]
  unfold Crossover.Received06.rowCanonicalMoment05
  simp only [heq]
  by_cases he : budget (Uniform07.capacity m) 0 X=budget (Uniform07.capacity m) 1 X
  · rw [if_pos he,decoded_equal_count_moment row X hX he i q]
    change (if budget (Uniform07.capacity m) 0 X=budget (Uniform07.capacity m) 1 X then
        privateCountMoment _ _ _ _ _ _ _ _ else 0)+
      (if numericRivalHasSeed row i z then
        finiteCanonicalPart _ _ _ _ _ _ _ _ X i q else 0)=_
    rw [if_pos he,finiteCanonicalPart_formula,if_pos he]
    simp only [ite_self,add_zero]
    rfl
  · rw [if_neg he]
    have hpart := decoded_finiteCanonicalPart row G hm X hX h0 hU he i q
    change (if budget (Uniform07.capacity m) 0 X=budget (Uniform07.capacity m) 1 X then
        privateCountMoment _ _ _ _ _ _ _ _ else 0)+
      (if numericRivalHasSeed row i z then
        finiteCanonicalPart _ _ _ _ _ _ _ _ X i q else 0)=_
    rw [if_neg he,zero_add]
    by_cases hs : (own:ℝ)≤ Uniform07.cutoff row/2
    · have hΛ : (54/100:ℝ)*Uniform07.cutoff row< G.multiplier := by
        simpa only [Uniform05.t_eq_canonical] using G.multiplier_guards.1
      have hR : 0< Early.bidCap row := by simpa only [cap_eq] using Uniform05.cap_pos row
      have hg : Uniform07.kappa row*Early.bidCap row< G.multiplier-Early.nativeRadius row :=
        (le_max_left _ _).trans_lt (((Early.native_sampling_margin_guards row).2 G.multiplier hΛ).1)
      have hzero : finiteCanonicalPart (Uniform07.xi row) (Uniform07.xi_pos row)
          (source_xi_lt_one row) G.multiplier (Early.demandRatio row) (Early.bidCap row)
          (Uniform07.capacity m)
          (literalSourceAlpha row G.multiplier G.rejectionRoot
            (10*UniformFinite.Source.commonGuardMargin row) (UniformFinite.Source.commonGuardMargin row)) X i q=0 := by
        unfold finiteCanonicalPart
        apply integral_eq_zero_of_ae
        exact ae_of_all _ fun s=>by
          simpa only [literalSourceAlpha,Pi.zero_apply] using
            literal_canonicalCountPart_seed_focal_zero row
              (zG:=G.rejectionRoot) (width:=10*UniformFinite.Source.commonGuardMargin row)
              hΛ hR hg hm (UniformFinite.Source.common_guard_margin row)
              (Uniform07.capacity m) (some s) X h0 hU i (hi.trans_le hs) q hq
      rw [hzero]
      simp only [ite_self]
      unfold UniformFinite.Source.guardAlpha
      split_ifs
      · simp only [zero_mul]
      · exact (hpart.symm.trans hzero).symm
    · have hseed := numeric_context_seed_iff row i own z
      have hh : (0< UniformFinite.Source.seedCount row (UniformFinite.NativeContext.decode X)
          (fun k=>entryBid (X.1 k))) ↔ numericRivalHasSeed row i z := by
        simpa only [hs,false_or] using hseed
      unfold UniformFinite.Source.guardAlpha
      by_cases hn : UniformFinite.Source.seedCount row (UniformFinite.NativeContext.decode X)
          (fun k=>entryBid (X.1 k))=0
      · have hns : ¬numericRivalHasSeed row i z := by
          intro hh'
          have hpos := hh.mpr hh'
          omega
        simp only [hn,if_true,hns,if_false,zero_mul]
      · have hsp : numericRivalHasSeed row i z := hh.mp (Nat.pos_of_ne_zero hn)
        simp only [hn,if_false,hsp,if_true]
        exact hpart

theorem native_canonical_count_numeric (E : UniformFinite.ExactRestrictedLaw row m)
    (hc : 1≤ Uniform07.capacity m) {R : ℝ} (hR : 0< R)
    (hUR : Early.bidCap row< R) (hRt : R< Uniform07.cutoff row)
    (hguard : Uniform07.kappa row*R< E.law.multiplier-Early.nativeRadius row)
    (i : Fin m) (a : JointAction 2) (ha0 : 0< a.bid) (haR : a.bid< R)
    (ha2 : a.routeCount=2) (q : Fin 3→ℝ) (hq : q 0=0) :
    nativeCanonicalMoment E hc R i a q=
      ∫z,nativeCanonicalNumericMoment row E.law i a.bid q z
        ∂Measure.pi (fun _ : Fin m=>UniformFinite.numericObservationLaw row E.law) := by
  have hzG : Uniform07.cutoff row/2≤ E.law.rejectionRoot := by
    have hz := (rejection_root_bounds E).1
    have ht := Uniform07.cutoff_pos row
    linarith only [hz,ht]
  rw [nativeCanonicalMoment,nativeGame,sourceNativeGame_canonical_count_expect_physical row
    E.cluster.market_two_le hc hR hUR hRt (multiplier_lower E) hguard hzG
    (UniformFinite.Source.common_guard_margin row) (lowerJoint E)
    (lowerJoint_value E) (lowerJoint_routes E) (lowerJoint_atomless E)
    i a ha0 haR ha2 q hq]
  let Γ := nativeGame E hc R
  let Z := fun d : UserProfile m 2=>fun j=>UniformFinite.OriginalPopulation.numericalDraw row (d j)
  let f := nativeCanonicalNumericMoment row E.law i a.bid q
  have hZ : Measurable Z := measurable_pi_lambda _ (fun j=>
    (UniformFinite.OriginalPopulation.measurable_numericalDraw row).comp (measurable_pi_apply j))
  have hf : Measurable f := measurable_nativeCanonicalNumericMoment row E.law i a.bid q
  have hshape := sourceNativeGame_profile_shape row E.cluster.market_two_le hc hR hRt
    (source_guard_multiplier_positive row (multiplier_lower E)) (lowerJoint E)
    (lowerJoint_value E) (lowerJoint_routes E)
    (literalSourceAlpha row E.law.multiplier E.law.rejectionRoot
      (10*UniformFinite.Source.commonGuardMargin row) (UniformFinite.Source.commonGuardMargin row))
    (measurable_literalSourceAlpha row (multiplier_lower E) E.law.rejectionRoot
      (10*UniformFinite.Source.commonGuardMargin row) (UniformFinite.Source.commonGuardMargin row))
  have hfg : (fun x : UserProfile m 2×Equiv.Perm (Fin 2)=>
      sourceCanonicalPhysicalTestOfRow row R E.law.multiplier E.law.rejectionRoot
        (10*UniformFinite.Source.commonGuardMargin row) (UniformFinite.Source.commonGuardMargin row)
        i a q x)=ᵐ[(userProfileLaw Γ).prod (permLaw 2)] (fun x=>f (Z x.1)) := by
    filter_upwards [(measurePreserving_fst (μ:=userProfileLaw Γ)
      (ν:=permLaw 2)).quasiMeasurePreserving.ae hshape] with x hx
    unfold sourceCanonicalPhysicalTestOfRow
    rw [focalInputContext_eq_numeric row hUR i a haR ha2 x.1 hx x.2,
      rivalHasSeed_eq_numeric row hUR i x.1 hx]
    rfl
  change (∫x,sourceCanonicalPhysicalTestOfRow row R E.law.multiplier E.law.rejectionRoot
    (10*UniformFinite.Source.commonGuardMargin row) (UniformFinite.Source.commonGuardMargin row)
    i a q x ∂(userProfileLaw Γ).prod (permLaw 2))=_
  rw [integral_congr_ae hfg]
  calc
    (∫x,f (Z x.1) ∂(userProfileLaw Γ).prod (permLaw 2))=
        ∫d,f (Z d) ∂((userProfileLaw Γ).prod (permLaw 2)).map Prod.fst :=
      (integral_map measurable_fst.aemeasurable (hf.comp hZ).aestronglyMeasurable).symm
    _=∫d,f (Z d) ∂userProfileLaw Γ := by
      rw [(measurePreserving_fst (μ:=userProfileLaw Γ) (ν:=permLaw 2)).map_eq]
    _=_ := by
      rw [←native_numeric_profile_law E hc hR hUR hRt]
      exact (integral_map hZ.aemeasurable hf.aestronglyMeasurable).symm

theorem native_canonical_count_eq05 (E : UniformFinite.ExactRestrictedLaw row m)
    (hc : 1≤ Uniform07.capacity m) {R : ℝ} (hR : 0< R)
    (hUR : Early.bidCap row< R) (hRt : R< Uniform07.cutoff row)
    (hguard : Uniform07.kappa row*R< E.law.multiplier-Early.nativeRadius row)
    (i : Fin m) (own : Uniform05.Bid row) (hown : 0<(own:ℝ))
    (q : Fin 3→ℝ) (hq : q 0=0) :
    nativeCanonicalMoment E hc R i (Hybrid.lowBroadcast own) q=
      ∫z,Crossover.Received06.rowCanonicalMoment05 row E.law
        (UniformFinite.Late.ExceptionalProfile.numericRow row i z)
        (UniformFinite.Late.ExceptionalProfile.numericBids row i own z) i q
        ∂Measure.pi (fun _ : Fin m=>UniformFinite.numericObservationLaw row E.law) := by
  letI : NeZero m := E.marketNeZero
  have hm : 0< m := lt_of_lt_of_le (by norm_num : 0<2) E.cluster.market_two_le
  have hownU : (own:ℝ)≤Early.bidCap row := by
    rw [←cap_eq]
    exact own.property.2
  have haR : (own:ℝ)< R := hownU.trans_lt hUR
  rw [native_canonical_count_numeric E hc hR hUR hRt hguard i
    (Hybrid.lowBroadcast own) hown haR rfl q hq]
  exact integral_congr_ae (ae_of_all _ (fun z=>numeric_canonical_moment_eq05 row E.law hm i own z q hq))

end FCAppendix.Affine.Uniform07Finishing.Concrete05
