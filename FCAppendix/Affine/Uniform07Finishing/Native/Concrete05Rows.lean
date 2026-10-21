import FCAppendix.Affine.Uniform07Finishing.Native.Concrete05Policy
import FCAppendix.Affine.Uniform07Finishing.Native.Concrete05Counts

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing.Concrete05
open Set MeasureTheory ProbabilityTheory Filter Topology Classical Game Bayes
open FCAppendix.Affine UniformFinite StrictNative Weighted
open scoped BigOperators

variable {row : Uniform07.Row} {m : ℕ} [Nonempty (Fin m)]

local instance : NeZero m := ⟨by
  have hi := (Classical.choice (inferInstance : Nonempty (Fin m))).isLt
  omega⟩

def nativeGame (E : UniformFinite.ExactRestrictedLaw row m)
    (hc : 1≤ Uniform07.capacity m) (R : ℝ) :
    FiniteGame m 2 (Uniform07.capacity m) unitInterval :=
  sourceNativeGame row hc R E.law.multiplier
    (source_guard_multiplier_positive row (multiplier_lower E)) (lowerJoint E)
    (literalSourceAlpha row E.law.multiplier E.law.rejectionRoot
      (10*UniformFinite.Source.commonGuardMargin row)
      (UniformFinite.Source.commonGuardMargin row))
    (measurable_literalSourceAlpha row (multiplier_lower E) E.law.rejectionRoot
      (10*UniformFinite.Source.commonGuardMargin row)
      (UniformFinite.Source.commonGuardMargin row))

theorem native_user_law_eq_original (E : UniformFinite.ExactRestrictedLaw row m)
    (hc : 1≤ Uniform07.capacity m) {R : ℝ} (hR : 0< R)
    (hRt : R< Uniform07.cutoff row) :
    userLaw (nativeGame E hc R)=userLaw (UniformFinite.OriginalPopulation.game E
      (upperPriorityLaw row m E.cluster.market_two_le hc R hR hRt)) := by
  letI : NeZero m := E.marketNeZero
  rw [nativeGame,sourceNativeGame_user_law row E.cluster.market_two_le hc hR hRt
    (source_guard_multiplier_positive row (multiplier_lower E)) (lowerJoint E)
    (lowerJoint_value E) (lowerJoint_routes E)]
  rw [userLaw,UniformFinite.OriginalPopulation.game_joint,
    UniformFinite.OriginalPopulation.fullLaw_mixture,sourcePopulation_literal,
    upperPriorityLaw_joint row m E.cluster.market_two_le hc R hR hRt]
  simp only [Uniform05.t_eq_canonical,lowerJoint]

theorem native_numeric_user_law (E : UniformFinite.ExactRestrictedLaw row m)
    (hc : 1≤ Uniform07.capacity m) {R : ℝ} (hR : 0< R)
    (hUR : Early.bidCap row< R) (hRt : R< Uniform07.cutoff row) :
    (userLaw (nativeGame E hc R)).map (UniformFinite.OriginalPopulation.numericalDraw row)=
      UniformFinite.numericObservationLaw row E.law := by
  letI : NeZero m := E.marketNeZero
  rw [native_user_law_eq_original E hc hR hRt]
  exact UniformFinite.OriginalPopulation.game_numeric_row_law E _ (by simpa [cap_eq] using hUR)

theorem native_numeric_profile_law (E : UniformFinite.ExactRestrictedLaw row m)
    (hc : 1≤ Uniform07.capacity m) {R : ℝ} (hR : 0< R)
    (hUR : Early.bidCap row< R) (hRt : R< Uniform07.cutoff row) :
    (userProfileLaw (nativeGame E hc R)).map
      (fun d : UserProfile m 2=>fun j=>UniformFinite.OriginalPopulation.numericalDraw row (d j))=
      Measure.pi (fun _ : Fin m=>UniformFinite.numericObservationLaw row E.law) := by
  unfold userProfileLaw
  rw [Measure.pi_map_pi
    (fun _=>(UniformFinite.OriginalPopulation.measurable_numericalDraw row).aemeasurable)]
  simp_rw [native_numeric_user_law E hc hR hUR hRt]

theorem native_deleted_numeric_rows {N : ℕ}
    (E : UniformFinite.ExactRestrictedLaw row (N+1))
    (hc : 1≤ Uniform07.capacity (N+1)) {R : ℝ} (hR : 0< R)
    (hUR : Early.bidCap row< R) (hRt : R< Uniform07.cutoff row) (i : Fin (N+1)) :
    (userProfileLaw (nativeGame E hc R)).map
      (fun d=>fun j : Fin N=>UniformFinite.OriginalPopulation.numericalDraw row (d (i.succAbove j)))=
      Measure.pi (fun _ : Fin N=>UniformFinite.numericObservationLaw row E.law) := by
  let H := upperPriorityLaw row (N+1) E.cluster.market_two_le hc R hR hRt
  have hp : userProfileLaw (nativeGame E hc R)=userProfileLaw
      (UniformFinite.OriginalPopulation.game E H) := by
    unfold userProfileLaw
    rw [native_user_law_eq_original E hc hR hRt]
  rw [hp]
  exact UniformFinite.OriginalPopulation.game_deleted_numeric_rows E H
    (by simpa [cap_eq] using hUR) i

theorem native_two_deleted_numeric_rows {N : ℕ}
    (E : UniformFinite.ExactRestrictedLaw row (N+2))
    (hc : 1≤ Uniform07.capacity (N+2)) {R : ℝ} (hR : 0< R)
    (hUR : Early.bidCap row< R) (hRt : R< Uniform07.cutoff row)
    (i : Fin (N+2)) (j : Fin (N+1)) :
    (userProfileLaw (nativeGame E hc R)).map
      (fun d=>fun k : Fin N=>UniformFinite.OriginalPopulation.numericalDraw row
        (d (i.succAbove (j.succAbove k))))=
      Measure.pi (fun _ : Fin N=>UniformFinite.numericObservationLaw row E.law) := by
  let H := upperPriorityLaw row (N+2) E.cluster.market_two_le hc R hR hRt
  have hp : userProfileLaw (nativeGame E hc R)=userProfileLaw
      (UniformFinite.OriginalPopulation.game E H) := by
    unfold userProfileLaw
    rw [native_user_law_eq_original E hc hR hRt]
  rw [hp]
  exact UniformFinite.OriginalPopulation.game_two_deleted_numeric_rows E H
    (by simpa [cap_eq] using hUR) i j

omit [Nonempty (Fin m)] in
theorem actualContext_eq_received {R : ℝ} (d : UserProfile m 2)
    (hd : d∈StrictNative.classifiedProfiles m R) :
    StrictNative.actualContext R d=UniformFinite.Late.Strict.actualContext R d := by
  apply Prod.ext
  · change StrictNative.broadcastPart R (observe (drawsRealization d) 0)=
      UniformFinite.Late.Strict.lowerPart R (observe (drawsRealization d) 0)
    rw [StrictNative.broadcastPart_observe d hd 0,
      UniformFinite.Late.Strict.lowerPart_observe d hd 0]
  · rfl

omit [Nonempty (Fin m)] in

theorem focalInputContext_eq_numeric (row : Uniform07.Row) {R : ℝ}
    (hUR : Early.bidCap row< R) (i : Fin m) (a : JointAction 2)
    (haR : a.bid< R) (ha2 : a.routeCount=2) (d : UserProfile m 2)
    (hd : ∀j,sourceDrawShape (Early.bidCap row) R (d j))
    (τ : Equiv.Perm (Fin 2)) :
    focalInputContext R i a (d,τ)=
      UniformFinite.Late.ExceptionalProfile.numericContext row i a.bid
        (fun j=>UniformFinite.OriginalPopulation.numericalDraw row (d j)) := by
  let d' := Function.update d i ((0,a),τ)
  have hd' : d'∈StrictNative.classifiedProfiles m R :=
    updated_broadcast_classified d (sourceDrawShape_classified hUR hd) i 0 a haR ha2 τ
  have hX : focalInputContext R i a (d,τ)=StrictNative.actualContext R d' := by
    rw [focalInputContext,deviationList_eq_focalLocalList]
    simp only [focalLocalList,insert_deleteFocal]
    exact StrictNative.observedContext_eq_actual d' hd' 0
  rw [hX,actualContext_eq_received d' hd']
  apply UniformFinite.Late.ExceptionalProfile.actualContext_inserted row
    (by simpa [cap_eq] using hUR) i a haR ha2 0 d _ τ
  simpa only [UniformFinite.Late.Strict.strongProfiles,sourceDrawShape,cap_eq,Set.mem_setOf_eq] using hd

def numericRivalHasSeed (row : Uniform07.Row) (i : Fin m)
    (z : Fin m→ UniformFinite.NumericObservation row) : Prop :=
  ∃j : RivalIndex i, UniformFinite.numericKind row (z j)=0 ∧
    UniformFinite.numericBid row (z j)≤ Uniform07.cutoff row/2

omit [Nonempty (Fin m)] in
theorem measurableSet_numericRivalHasSeed (row : Uniform07.Row) (i : Fin m) :
    MeasurableSet {z | numericRivalHasSeed row i z} := by
  simp only [numericRivalHasSeed,setOf_exists]
  apply MeasurableSet.iUnion
  intro j
  exact (measurableSet_eq_fun
    ((UniformFinite.measurable_numericKind row).comp (measurable_pi_apply (j : Fin m)))
    measurable_const).inter (measurableSet_le
      ((UniformFinite.measurable_numericBid row).comp (measurable_pi_apply (j : Fin m))) measurable_const)

omit [Nonempty (Fin m)] in
theorem rivalHasSeed_eq_numeric (row : Uniform07.Row) {R : ℝ}
    (hUR : Early.bidCap row< R) (i : Fin m) (d : UserProfile m 2)
    (hd : ∀j,sourceDrawShape (Early.bidCap row) R (d j)) :
    rivalHasSeed (Uniform07.cutoff row/2) i (deleteFocal i d) ↔
      numericRivalHasSeed row i
        (fun j=>UniformFinite.OriginalPopulation.numericalDraw row (d j)) := by
  have hzU := source_seed_cutoff_lt_bidCap row
  apply exists_congr
  intro j
  dsimp only [deleteFocal]
  rcases hd j with ⟨hb,hr⟩|⟨hb,hr⟩
  · have hb' : (d j).1.2.bid≤ Uniform05.cap row := by simpa [cap_eq] using hb
    rw [UniformFinite.NativeProfile.numericalDraw_lower row (d j) hb']
    simp [UniformFinite.numericKind,UniformFinite.numericBid,
      UniformFinite.OriginalPopulation.clipBid,max_eq_right (d j).1.2.bid_nonneg,
      min_eq_right hb']
  · have hb' : Uniform05.cap row<(d j).1.2.bid := by
      simpa [cap_eq] using hUR.trans_le hb
    rw [UniformFinite.NativeProfile.numericalDraw_upper row (d j) hb']
    have hn : ¬(d j).1.2.bid≤ Uniform07.cutoff row/2 :=
      not_le.mpr (hzU.trans (hUR.trans_le hb))
    by_cases hj : (0:Fin 2)∈firstK (d j).2 1 <;>
      simp [UniformFinite.numericKind,UniformFinite.numericBid,hj,hn]

def nativeNumericCountMoment (row : Uniform07.Row) (G : Uniform05.RestrictedLaw row)
    (i : Fin m) (own : ℝ) (q : Fin 3→ℝ)
    (z : Fin m→ UniformFinite.NumericObservation row) : ℝ :=
  nativeContextCountMoment row G
    (UniformFinite.Late.ExceptionalProfile.numericContext row i own z)
    (numericRivalHasSeed row i z) i q

theorem measurable_nativeNumericCountMoment (row : Uniform07.Row)
    (G : Uniform05.RestrictedLaw row) (i : Fin m) (own : ℝ) (q : Fin 3→ℝ) :
    Measurable (nativeNumericCountMoment row G i own q) := by
  have hX := UniformFinite.Late.ExceptionalProfile.measurable_numericContext row i own
  have hΛ : (54/100:ℝ)*Uniform07.cutoff row< G.multiplier := by
    simpa only [Uniform05.t_eq_canonical] using G.multiplier_guards.1
  unfold nativeNumericCountMoment nativeContextCountMoment
  exact ((measurable_privateCountMoment (Uniform07.xi row) (Uniform07.xi_pos row)
    (source_xi_lt_one row) (Uniform07.capacity m) i q).comp
      (hX.prodMk measurable_const)).add
    (Measurable.ite (measurableSet_numericRivalHasSeed row i)
      ((measurable_finitePathCountCorrection (Uniform07.xi row) (Uniform07.xi_pos row)
        (source_xi_lt_one row) G.multiplier (Early.demandRatio row) (Early.bidCap row)
        (source_guard_multiplier_positive row hΛ) (Uniform07.capacity m)
        (literalSourceAlpha row G.multiplier G.rejectionRoot
          (10*UniformFinite.Source.commonGuardMargin row) (UniformFinite.Source.commonGuardMargin row))
        (measurable_literalSourceAlpha row hΛ G.rejectionRoot
          (10*UniformFinite.Source.commonGuardMargin row) (UniformFinite.Source.commonGuardMargin row))
        i q).comp hX) measurable_const)

theorem abs_nativeNumericCountMoment_le (row : Uniform07.Row)
    (G : Uniform05.RestrictedLaw row) (i : Fin m) (own : ℝ) (q : Fin 3→ℝ)
    (z : Fin m→ UniformFinite.NumericObservation row) :
    |nativeNumericCountMoment row G i own q z|≤ 3*∑k : Fin 3,|q k| := by
  let X := UniformFinite.Late.ExceptionalProfile.numericContext row i own z
  have hB := abs_privateCountMoment_le (Uniform07.xi row) (Uniform07.xi_pos row)
    (source_xi_lt_one row) (Uniform07.capacity m) X none i q
  have hC := abs_finitePathCountCorrection_le (Uniform07.xi row) (Uniform07.xi_pos row)
    (source_xi_lt_one row) G.multiplier (Early.demandRatio row) (Early.bidCap row)
    (Uniform07.capacity m)
    (literalSourceAlpha row G.multiplier G.rejectionRoot
      (10*UniformFinite.Source.commonGuardMargin row) (UniformFinite.Source.commonGuardMargin row)) X i q
  dsimp only [literalSourceAlpha, X] at hB hC
  have hq : 0≤∑k : Fin 3,|q k| := Finset.sum_nonneg (fun _ _=>abs_nonneg _)
  unfold nativeNumericCountMoment nativeContextCountMoment
  split_ifs
  · exact (abs_add_le _ _).trans (by linarith)
  · simpa only [add_zero] using hB.trans (by linarith)

theorem native_broadcast_count_numeric (E : UniformFinite.ExactRestrictedLaw row m)
    (hc : 1≤ Uniform07.capacity m) {R : ℝ} (hR : 0< R)
    (hUR : Early.bidCap row< R) (hRt : R< Uniform07.cutoff row)
    (hguard : Uniform07.kappa row*R< E.law.multiplier-Early.nativeRadius row)
    (i : Fin m) (a : JointAction 2) (ha0 : 0< a.bid) (haR : a.bid< R)
    (ha2 : a.routeCount=2) (q : Fin 3→ℝ) :
    ((problem (nativeGame E hc R) i).outcome a).expect q=
      ∫z,nativeNumericCountMoment row E.law i a.bid q z
        ∂Measure.pi (fun _ : Fin m=>UniformFinite.numericObservationLaw row E.law) := by
  have hzG : Uniform07.cutoff row/2≤ E.law.rejectionRoot := by
    have hz := (rejection_root_bounds E).1
    have ht := Uniform07.cutoff_pos row
    linarith only [hz,ht]
  rw [nativeGame,sourceNativeGame_broadcast_count_expect_physical row
    E.cluster.market_two_le hc hR hUR hRt (multiplier_lower E) hguard hzG
    (UniformFinite.Source.common_guard_margin row) (lowerJoint E)
    (lowerJoint_value E) (lowerJoint_routes E) (lowerJoint_atomless E)
    i a ha0 haR ha2 q]
  let Γ := nativeGame E hc R
  let Z := fun d : UserProfile m 2=>fun j=>UniformFinite.OriginalPopulation.numericalDraw row (d j)
  let f := nativeNumericCountMoment row E.law i a.bid q
  have hZ : Measurable Z := measurable_pi_lambda _ (fun j=>
    (UniformFinite.OriginalPopulation.measurable_numericalDraw row).comp (measurable_pi_apply j))
  have hf : Measurable f := measurable_nativeNumericCountMoment row E.law i a.bid q
  have hshape := sourceNativeGame_profile_shape row E.cluster.market_two_le hc hR hRt
    (source_guard_multiplier_positive row (multiplier_lower E)) (lowerJoint E)
    (lowerJoint_value E) (lowerJoint_routes E)
    (literalSourceAlpha row E.law.multiplier E.law.rejectionRoot
      (10*UniformFinite.Source.commonGuardMargin row) (UniformFinite.Source.commonGuardMargin row))
    (measurable_literalSourceAlpha row (multiplier_lower E) E.law.rejectionRoot
      (10*UniformFinite.Source.commonGuardMargin row) (UniformFinite.Source.commonGuardMargin row))
  have hfg : (fun x : UserProfile m 2×Equiv.Perm (Fin 2)=>
      sourcePhysicalCountTestOfRow row R E.law.multiplier E.law.rejectionRoot
        (10*UniformFinite.Source.commonGuardMargin row) (UniformFinite.Source.commonGuardMargin row)
        i a q x)=ᵐ[(userProfileLaw Γ).prod (permLaw 2)] (fun x=>f (Z x.1)) := by
    filter_upwards [(measurePreserving_fst (μ:=userProfileLaw Γ)
      (ν:=permLaw 2)).quasiMeasurePreserving.ae hshape] with x hx
    unfold sourcePhysicalCountTestOfRow sourcePhysicalCountTest
    rw [focalInputContext_eq_numeric row hUR i a haR ha2 x.1 hx x.2,
      rivalHasSeed_eq_numeric row hUR i x.1 hx]
    rfl
  calc
    _ = ∫x,f (Z x.1) ∂(userProfileLaw Γ).prod (permLaw 2) := by
      convert! integral_congr_ae hfg using 1
    _=
        ∫d,f (Z d) ∂((userProfileLaw Γ).prod (permLaw 2)).map Prod.fst :=
      (integral_map measurable_fst.aemeasurable (hf.comp hZ).aestronglyMeasurable).symm
    _=∫d,f (Z d) ∂userProfileLaw Γ := by
      rw [(measurePreserving_fst (μ:=userProfileLaw Γ) (ν:=permLaw 2)).map_eq]
    _=_ := by
      rw [←native_numeric_profile_law E hc hR hUR hRt]
      exact (integral_map hZ.aemeasurable hf.aestronglyMeasurable).symm

end FCAppendix.Affine.Uniform07Finishing.Concrete05
