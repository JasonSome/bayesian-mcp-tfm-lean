import FCAppendix.Affine.Uniform07Finishing.Native.Concrete05AboveCapMenu
import FCAppendix.Affine.Uniform07Finishing.Native.SourceSuccessBadEvents

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing.Concrete05
open MeasureTheory ProbabilityTheory Game Bayes Set Filter Topology Classical
open FCAppendix.Affine StrictNative ConditionalSuccess
open scoped BigOperators
variable {M : ℕ} [Nonempty (Fin M)]

omit [Nonempty (Fin M)] in
theorem sourcePolicySlacks_loss_one_of_weight_mono (i : Uniform07.Row) {Λ z width : ℝ}
    (hΛ : (54/100:ℝ)*Uniform07.cutoff i<Λ)
    (X Y : StrictNative.ClassifiedContext M) (a : Fin M)
    (hpres : Weighted.presentSet X.1=Weighted.presentSet Y.1) (hup : X.2=Y.2)
    (hrest : ∀j, j≠a → X.1 j=Y.1 j)
    (hw : WeightedSampling.totalWeight
      (Weighted.sourceWeights (Uniform07.xi i) Λ (Early.demandRatio i) (Early.bidCap i) X.1)≤
      WeightedSampling.totalWeight
      (Weighted.sourceWeights (Uniform07.xi i) Λ (Early.demandRatio i) (Early.bidCap i) Y.1)) :
    ∀k : Fin 7,
      Weighted.sourcePolicySlacks (Uniform07.xi i) Λ (Early.nativeRadius i)
        (Early.demandRatio i) (Early.bidCap i) (Uniform07.cutoff i/1000) z
        (Uniform07.cutoff i) width (Uniform07.capacity M) X k-1≤
      Weighted.sourcePolicySlacks (Uniform07.xi i) Λ (Early.nativeRadius i)
        (Early.demandRatio i) (Early.bidCap i) (Uniform07.cutoff i/1000) z
        (Uniform07.cutoff i) width (Uniform07.capacity M) Y k := by
  have hlo:=source_guard_root_positive i hΛ
  have hhi : 0<Λ+Early.nativeRadius i := by
    have ha:=(Early.native_sampling_margin_guards i).1
    linarith
  have hd : 0< Uniform07.cutoff i/1000 := div_pos (Uniform07.cutoff_pos i) (by norm_num)
  have hb (j : Fin 2) : Weighted.budget (Uniform07.capacity M) j X=
      Weighted.budget (Uniform07.capacity M) j Y := by
    simp only [Weighted.budget,StrictNative.contextUpper,hpres,hup]
  have hLo := sum_unit_change_le
    (fun j=>ClippedResidual.exposure (Uniform07.xi i) (Λ-Early.nativeRadius i) (entryBid (X.1 j)))
    (fun j=>ClippedResidual.exposure (Uniform07.xi i) (Λ-Early.nativeRadius i) (entryBid (Y.1 j)))
    a (fun j hj=>by rw [hrest j hj]) (ClippedResidual.exposure_le_one _ _ _)
    (ClippedResidual.exposure_nonneg (Uniform07.xi_pos i) hlo)
  have hHi := sum_unit_change_le
    (fun j=>ClippedResidual.exposure (Uniform07.xi i) (Λ+Early.nativeRadius i) (entryBid (Y.1 j)))
    (fun j=>ClippedResidual.exposure (Uniform07.xi i) (Λ+Early.nativeRadius i) (entryBid (X.1 j)))
    a (fun j hj=>by rw [hrest j hj]) (ClippedResidual.exposure_le_one _ _ _)
    (ClippedResidual.exposure_nonneg (Uniform07.xi_pos i) hhi)
  have hZ := sum_unit_change_le
    (fun j=>Weighted.sourcePsi (Uniform07.cutoff i/1000) z (entryBid (X.1 j)))
    (fun j=>Weighted.sourcePsi (Uniform07.cutoff i/1000) z (entryBid (Y.1 j)))
    a (fun j hj=>by rw [hrest j hj]) (Weighted.sourcePsi_le_one hd)
    (by unfold Weighted.sourcePsi; positivity)
  intro k
  fin_cases k
  · change (Weighted.sourceDemand (Uniform07.xi i) (Λ-Early.nativeRadius i) X.1-(Weighted.commonBudget (Uniform07.capacity M) X:ℝ)-((max (Weighted.budget (Uniform07.capacity M) 0 X) (Weighted.budget (Uniform07.capacity M) 1 X)-Weighted.commonBudget (Uniform07.capacity M) X:ℕ):ℝ))-1≤(Weighted.sourceDemand (Uniform07.xi i) (Λ-Early.nativeRadius i) Y.1-(Weighted.commonBudget (Uniform07.capacity M) Y:ℝ)-((max (Weighted.budget (Uniform07.capacity M) 0 Y) (Weighted.budget (Uniform07.capacity M) 1 Y)-Weighted.commonBudget (Uniform07.capacity M) Y:ℕ):ℝ))
    simp only [Weighted.commonBudget,hb]
    dsimp only [Weighted.sourceDemand]
    linarith only [hLo]
  · change ((Weighted.commonBudget (Uniform07.capacity M) X:ℝ)-Weighted.sourceDemand (Uniform07.xi i) (Λ+Early.nativeRadius i) X.1)-1≤((Weighted.commonBudget (Uniform07.capacity M) Y:ℝ)-Weighted.sourceDemand (Uniform07.xi i) (Λ+Early.nativeRadius i) Y.1)
    simp only [Weighted.commonBudget,hb]
    dsimp only [Weighted.sourceDemand]
    linarith only [hHi]
  · change (WeightedSampling.totalWeight (Weighted.sourceWeights (Uniform07.xi i) Λ (Early.demandRatio i) (Early.bidCap i) X.1)-((max (Weighted.budget (Uniform07.capacity M) 0 X) (Weighted.budget (Uniform07.capacity M) 1 X)-Weighted.commonBudget (Uniform07.capacity M) X:ℕ):ℝ))-1≤(WeightedSampling.totalWeight (Weighted.sourceWeights (Uniform07.xi i) Λ (Early.demandRatio i) (Early.bidCap i) Y.1)-((max (Weighted.budget (Uniform07.capacity M) 0 Y) (Weighted.budget (Uniform07.capacity M) 1 Y)-Weighted.commonBudget (Uniform07.capacity M) Y:ℕ):ℝ))
    simp only [Weighted.commonBudget,hb]
    linarith only [hw]
  · change (Weighted.sourceRejectionDemand (Uniform07.cutoff i/1000) z X.1-(Weighted.budget (Uniform07.capacity M) 0 X:ℝ)-(Weighted.budget (Uniform07.capacity M) 1 X:ℝ))-1≤(Weighted.sourceRejectionDemand (Uniform07.cutoff i/1000) z Y.1-(Weighted.budget (Uniform07.capacity M) 0 Y:ℝ)-(Weighted.budget (Uniform07.capacity M) 1 Y:ℝ))
    simp only [hb]
    dsimp only [Weighted.sourceRejectionDemand]
    linarith only [hZ]
  · change (width*M-|((Weighted.presentSet X.1).card:ℝ)-Uniform07.cutoff i*M|)-1≤(width*M-|((Weighted.presentSet Y.1).card:ℝ)-Uniform07.cutoff i*M|)
    simp only [hpres]
    linarith
  · change (width*M-|(X.2.1:ℝ)-(1-Uniform07.cutoff i)*M/2|)-1≤(width*M-|(Y.2.1:ℝ)-(1-Uniform07.cutoff i)*M/2|)
    simp only [hup]
    linarith
  · change (width*M-|(X.2.2:ℝ)-(1-Uniform07.cutoff i)*M/2|)-1≤(width*M-|(Y.2.2:ℝ)-(1-Uniform07.cutoff i)*M/2|)
    simp only [hup]
    linarith

omit [Nonempty (Fin M)] in

theorem rowContext_zero_weight_mono (i : Uniform07.Row) (G : Uniform05.RestrictedLaw i)
    (row : UniformFinite.Source.CountRow M) (b : Fin M→ℝ) (a : Fin M)
    (ha : a∈row.lower) (hzero : b a=0) (own : ℝ) :
    WeightedSampling.totalWeight (Weighted.sourceWeights (Uniform07.xi i) G.multiplier
      (Early.demandRatio i) (Early.bidCap i) (rowContext row b).1)≤
    WeightedSampling.totalWeight (Weighted.sourceWeights (Uniform07.xi i) G.multiplier
      (Early.demandRatio i) (Early.bidCap i) (rowContext row (Function.update b a own)).1) := by
  apply Finset.sum_le_sum
  intro j _
  by_cases hj : j=a
  · subst j
    have hG : 0< G.multiplier := (Uniform05.demandLo_pos i).trans G.multiplier_guards.1
    have hz : ClippedResidual.exposure (Uniform07.xi i) G.multiplier 0=0 :=
      ClippedResidual.exposure_zero hG.le
    have hleft : (Weighted.sourceWeights (Uniform07.xi i) G.multiplier
        (Early.demandRatio i) (Early.bidCap i) (rowContext row b).1).1 a=0 := by
      simp only [Weighted.sourceWeights,rowContext,if_pos ha,Weighted.eligibleWeight,
        hzero,if_pos (native_cap_positive i).le,hz,
        Weighted.guardWeight_zero (Early.demandRatio_pos i)
          (div_nonneg (Early.demandRatio_pos i).le (by norm_num))]
    rw [hleft]
    exact ((Weighted.sourceWeights _ _ _ _ _).property a).1
  · simp only [Weighted.sourceWeights,rowContext,Function.update_of_ne hj,le_refl]

omit [Nonempty (Fin M)] in

theorem native_policy_inner_of_source_control (i : Uniform07.Row)
    (G : Uniform05.RestrictedLaw i) (x : Fin M→ UniformFinite.Source.Observation i)
    (a : Fin M) (ha : a∈(UniformFinite.Source.observationCountRow i x).lower)
    (hzero : UniformFinite.Source.observationBid i (x a)=0) (hM : 0< M)
    (hc : |(Uniform07.capacity M:ℝ)/M-Uniform05.rho|≤ UniformFinite.Source.commonGuardMargin i)
    (hx : ∀k : Fin 8, |(∑j,UniformFinite.Source.sourceStatistic i G k (x j))/(M:ℝ)-
      UniformFinite.Source.sourceMean i G k|≤ UniformFinite.Source.commonGuardMargin i)
    (hsize : 1≤ UniformFinite.Source.commonGuardMargin i*M)
    (own : ℝ) : ∀k : Fin 7,
    2*(UniformFinite.Source.commonGuardMargin i*M)≤
      Weighted.sourcePolicySlacks (Uniform07.xi i) G.multiplier (Early.nativeRadius i)
        (Early.demandRatio i) (Early.bidCap i) (Uniform07.cutoff i/1000) G.rejectionRoot
        (Uniform07.cutoff i) (10*UniformFinite.Source.commonGuardMargin i)
        (Uniform07.capacity M)
        (rowContext (UniformFinite.Source.observationCountRow i x)
          (Function.update (fun j=>UniformFinite.Source.observationBid i (x j)) a own)) k := by
  let row:=UniformFinite.Source.observationCountRow i x
  let b:=fun j=>UniformFinite.Source.observationBid i (x j)
  let X:=rowContext row b
  let Y:=rowContext row (Function.update b a own)
  have hcap : ∀j,entryBid (X.1 j)≤ Early.bidCap i := by
    intro j
    have hentry : (fun j=>entryBid (X.1 j))=b := by
      simpa only [X,rowContext_entry] using UniformFinite.Source.lowerBids_observation i x
    rw [congrFun hentry j]
    rcases hxj : x j with p|k
    · simpa [b,UniformFinite.Source.observationBid,hxj,cap_eq] using p.2.property.2
    · simp only [b,UniformFinite.Source.observationBid,hxj]
      exact (native_cap_positive i).le
  have hΛ : (54/100:ℝ)*Uniform07.cutoff i< G.multiplier := by
    simpa only [Uniform05.t_eq_canonical] using G.multiplier_guards.1
  have hmargin:=sourceStatistic_control_slacks_eight i G x hM hc hx
  have hw:=rowContext_zero_weight_mono i G row b a ha hzero own
  have hloss:=sourcePolicySlacks_loss_one_of_weight_mono (z:=G.rejectionRoot)
    (width:=10*UniformFinite.Source.commonGuardMargin i) i hΛ X Y a
    (by simp only [X,Y,rowContext_present]) rfl
    (fun j hj=>by simp only [X,Y,rowContext,Function.update_of_ne hj]) hw
  have hMr : (0:ℝ)< M := by exact_mod_cast hM
  have he:=UniformFinite.Source.common_guard_margin i
  have hinner (k : Fin 7) : 2*(UniformFinite.Source.commonGuardMargin i*M)≤
      Weighted.sourcePolicySlacks (Uniform07.xi i) G.multiplier (Early.nativeRadius i)
        (Early.demandRatio i) (Early.bidCap i) (Uniform07.cutoff i/1000) G.rejectionRoot
        (Uniform07.cutoff i) (10*UniformFinite.Source.commonGuardMargin i)
        (Uniform07.capacity M) Y k := by
    have hnorm:=sourceSlacks_eq_sourcePolicySlacks i G hM X (rowContext_valid row b) hcap k
    dsimp only [X] at hnorm
    rw [rowContext_decode,rowContext_entry,UniformFinite.Source.lowerBids_observation i x] at hnorm
    have hh : 8*UniformFinite.Source.commonGuardMargin i≤
        Weighted.sourcePolicySlacks (Uniform07.xi i) G.multiplier (Early.nativeRadius i)
          (Early.demandRatio i) (Early.bidCap i) (Uniform07.cutoff i/1000) G.rejectionRoot
          (Uniform07.cutoff i) (10*UniformFinite.Source.commonGuardMargin i)
          (Uniform07.capacity M) X k/M := by
      rw [←hnorm]
      exact hmargin k
    have hh':= (le_div_iff₀ hMr).mp hh
    have hl:=hloss k
    nlinarith
  exact hinner

omit [Nonempty (Fin M)] in

theorem source_scalar_inner_of_policy_inner (i : Uniform07.Row) (Λ z width ε : ℝ)
    (X : ClassifiedContext M)
    (h : ∀k : Fin 7,2*(ε*M)≤ Weighted.sourcePolicySlacks (Uniform07.xi i) Λ
      (Early.nativeRadius i) (Early.demandRatio i) (Early.bidCap i)
      (Uniform07.cutoff i/1000) z (Uniform07.cutoff i) width (Uniform07.capacity M) X k) :
    ∀k : Fin 5,2*(ε*M)≤ sourceSuccessSlacks i Λ z width X k := by
  intro k
  fin_cases k
  · exact h 0
  · exact h 1
  · exact h 2
  · exact h 3
  · have h0:=h 4
    have h1:=h 5
    have h2:=h 6
    change 2*(ε*M)≤width*M-|((Weighted.presentSet X.1).card:ℝ)-Uniform07.cutoff i*M| at h0
    change 2*(ε*M)≤width*M-|(X.2.1:ℝ)-(1-Uniform07.cutoff i)*M/2| at h1
    change 2*(ε*M)≤width*M-|(X.2.2:ℝ)-(1-Uniform07.cutoff i)*M/2| at h2
    change 2*(ε*M)≤ width*M-max
      (abs (((Weighted.presentSet X.1).card:ℝ)-Uniform07.cutoff i*M))
      (max (abs ((X.2.1:ℝ)-(1-Uniform07.cutoff i)*M/2))
        (abs ((X.2.2:ℝ)-(1-Uniform07.cutoff i)*M/2)))
    have hm : max
        (abs (((Weighted.presentSet X.1).card:ℝ)-Uniform07.cutoff i*M))
        (max (abs ((X.2.1:ℝ)-(1-Uniform07.cutoff i)*M/2))
          (abs ((X.2.2:ℝ)-(1-Uniform07.cutoff i)*M/2)))≤ width*M-2*(ε*M) :=
      max_le (by linarith) (max_le (by linarith) (by linarith))
    linarith

omit [Nonempty (Fin M)] in

theorem contacted_list_eq_broadcast (i : Fin M) (a : JointAction 2)
    (d : UserProfile M 2) (τ : Equiv.Perm (Fin 2)) (j : Fin 2)
    (hcontact : deviationList i a d τ j i≠none) :
    deviationList i a d τ j=deviationList i (Crossover.Physical.two a.bid) d τ j := by
  have hj : j∈firstK τ a.routeCount := by
    by_contra hj
    exact hcontact (by simp [deviationList,observe,deviate,hj])
  funext u
  by_cases hu : u=i
  · subst u
    simp [deviationList,observe,deviate,hj,Crossover.Physical.two,
      Crossover.Physical.action,firstK_full_two,max_eq_left a.bid_nonneg]
  · simp [deviationList,observe,deviate,hu]

omit [Nonempty (Fin M)] in

theorem contacted_context_eq_numeric (row : Uniform07.Row) {R : ℝ}
    (hUR : Early.bidCap row< R) (i : Fin M) (a : JointAction 2) (haR : a.bid< R)
    (d : UserProfile M 2) (hd : ∀u,sourceDrawShape (Early.bidCap row) R (d u))
    (τ : Equiv.Perm (Fin 2)) (j : Fin 2)
    (hcontact : deviationList i a d τ j i≠none) :
    observedContext R j (deviationList i a d τ j)=
      UniformFinite.Late.ExceptionalProfile.numericContext row i a.bid
        (fun u=>UniformFinite.OriginalPopulation.numericalDraw row (d u)) := by
  let B:=Crossover.Physical.two a.bid
  have hB : B.bid=a.bid := Crossover.Physical.two_bid a.bid_nonneg
  have hBR : B.bid< R := by rw [hB]; exact haR
  let d':=Function.update d i ((0,B),τ)
  have hd' : d'∈StrictNative.classifiedProfiles M R :=
    updated_broadcast_classified d (sourceDrawShape_classified hUR hd) i 0 B hBR rfl τ
  rw [contacted_list_eq_broadcast i a d τ j hcontact]
  have hlist : deviationList i B d τ j=observe (drawsRealization d') j := by
    funext u
    by_cases hu : u=i
    · subst u
      simp [deviationList,observe,deviate,drawsRealization,d']
    · simp [deviationList,observe,deviate,drawsRealization,d',hu]
  rw [hlist,StrictNative.observedContext_eq_actual d' hd' j,
    actualContext_eq_received d' hd']
  have hctx:=UniformFinite.Late.ExceptionalProfile.actualContext_inserted row
    (by simpa [cap_eq] using hUR) i B hBR rfl 0 d
    (by simpa only [UniformFinite.Late.Strict.strongProfiles,sourceDrawShape,cap_eq,Set.mem_setOf_eq] using hd) τ
  simpa only [d',hB] using hctx

theorem native_scalar_guard_failure_le (row : Uniform07.Row)
    (E : UniformFinite.ExactRestrictedLaw row M) (hc : 1≤ Uniform07.capacity M)
    {R : ℝ} (hR : 0< R) (hUR : Early.bidCap row< R) (hRt : R< Uniform07.cutoff row)
    (hsize : 2/(M:ℝ)≤ UniformFinite.Source.commonGuardMargin row)
    (i : Fin M) (a : JointAction 2) (haR : a.bid< R)
    (τ : Equiv.Perm (Fin 2)) (j : Fin 2) (k : Fin 5) :
    (userProfileLaw (nativeGame E hc R)).real
      (sourceScalarGuardFailure row R E.law.multiplier E.law.rejectionRoot
        (10*UniformFinite.Source.commonGuardMargin row)
        (UniformFinite.Source.commonGuardMargin row) i a τ j k)≤
      18*Real.exp (-(M:ℝ)*(UniformFinite.Source.commonGuardMargin row)^2/2) := by
  letI : NeZero M:=E.marketNeZero
  let ε:=UniformFinite.Source.commonGuardMargin row
  let Γ:=nativeGame E hc R
  let Z:=fun d : UserProfile M 2=>fun u=>
    UniformFinite.OriginalPopulation.numericalDraw row (d u)
  let drop:=fun x : Fin M→ UniformFinite.Source.Observation row=>
    fun u=>UniformFinite.dropValue row (x u)
  let μ:=Measure.pi (fun _ : Fin M=>UniformFinite.Source.observationLaw row E.law)
  let ν:=Measure.pi (fun _ : Fin M=>UniformFinite.numericObservationLaw row E.law)
  let B : Set (Fin M→ UniformFinite.NumericObservation row):=
    {z|sourceSuccessSlacks row E.law.multiplier E.law.rejectionRoot (10*ε)
      (UniformFinite.Late.ExceptionalProfile.numericContext row i a.bid z) k<2*(ε*M)}
  let A:=sourceScalarGuardFailure row R E.law.multiplier E.law.rejectionRoot
    (10*ε) ε i a τ j k
  have hM : 0< M := by have hm:=E.cluster.market_two_le; omega
  have hMr : (0:ℝ)< M := by exact_mod_cast hM
  have hε : 0<ε := UniformFinite.Source.common_guard_margin row
  have hinv : 1/(M:ℝ)≤ε/2 := by
    have he : 2/(M:ℝ)=2*(1/(M:ℝ)) := by ring
    rw [he] at hsize
    change 1/(M:ℝ)≤ε/2
    change 2*(1/(M:ℝ))≤ε at hsize
    linarith only [hsize]
  have hcaperr : |(Uniform07.capacity M:ℝ)/M-Uniform05.rho|≤ε :=
    (UniformFinite.Source.capacity_error_le M hM).trans (by linarith only [hinv,hε])
  have hlarge : 1≤ε*M := by
    have htwo := (div_le_iff₀ hMr).mp hsize
    dsimp [ε] at *
    linarith
  have hZ : Measurable Z:=measurable_pi_lambda _ (fun u=>
    (UniformFinite.OriginalPopulation.measurable_numericalDraw row).comp (measurable_pi_apply u))
  have hdrop : Measurable drop:=measurable_pi_lambda _ (fun u=>
    (UniformFinite.measurable_dropValue row).comp (measurable_pi_apply u))
  have hB : MeasurableSet B := measurableSet_lt
    ((measurable_sourceSuccessSlacks row (multiplier_lower E) E.law.rejectionRoot (10*ε) k).comp
      (UniformFinite.Late.ExceptionalProfile.measurable_numericContext row i a.bid))
    measurable_const
  have hshape:=sourceNativeGame_profile_shape row E.cluster.market_two_le hc hR hRt
    (source_guard_multiplier_positive row (multiplier_lower E)) (lowerJoint E)
    (lowerJoint_value E) (lowerJoint_routes E)
    (literalSourceAlpha row E.law.multiplier E.law.rejectionRoot (10*ε) ε)
    (measurable_literalSourceAlpha row (multiplier_lower E) E.law.rejectionRoot (10*ε) ε)
  have hinc : ∀ᵐ d ∂userProfileLaw Γ,d∈A→ Z d∈B := by
    filter_upwards [hshape] with d hd
    intro hA
    have hctx:=contacted_context_eq_numeric row hUR i a haR d hd τ j hA.1
    simpa only [B,Z,hctx,Set.mem_setOf_eq] using hA.2
  have hprofile : (userProfileLaw Γ).real A≤ν.real B := by
    calc
      _≤(userProfileLaw Γ).real (Z ⁻¹' B) :=
        ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hinc)
      _=((userProfileLaw Γ).map Z).real B := by
        rw [Measure.real,Measure.real,Measure.map_apply hZ hB]
      _=ν.real B := by
        have heq : (userProfileLaw Γ).map Z=ν := by
          convert! native_numeric_profile_law E hc hR hUR hRt using 1
        rw [heq]
  have hobs : drop ⁻¹' B⊆
      {x|¬UniformFinite.Source.MenuGood row E.law ε (zeroFocalObservation row i x)} := by
    intro x hx hg
    have hs:=native_policy_inner_of_source_control row E.law (zeroFocalObservation row i x) i
      (zeroFocalObservation_mem row i x) (zeroFocalObservation_bid row i x) hM hcaperr
      (fun l=>(hg.1 l).le) hlarge a.bid
    have hh:=source_scalar_inner_of_policy_inner row E.law.multiplier E.law.rejectionRoot
      (10*ε) ε _ hs k
    have hctx:=numericContext_dropValue row i a.bid x
    change sourceSuccessSlacks row E.law.multiplier E.law.rejectionRoot (10*ε)
      (UniformFinite.Late.ExceptionalProfile.numericContext row i a.bid (drop x)) k<2*(ε*M) at hx
    rw [hctx] at hx
    exact (not_lt_of_ge hh) hx
  have hmap : μ.map drop=ν:=UniformFinite.dropValueRow_law row E.law M
  have htail:=updated_menu_bad_le row E.law i (zeroObservation row) hM hε.le hinv
  calc
    (userProfileLaw Γ).real A≤ν.real B:=hprofile
    _=μ.real (drop ⁻¹' B) := by rw [←hmap,Measure.real,Measure.map_apply hdrop hB]; rfl
    _≤μ.real {x|¬UniformFinite.Source.MenuGood row E.law ε (zeroFocalObservation row i x)}:=
      measureReal_mono hobs
    _≤ 18*Real.exp (-(M:ℝ)*ε^2/2):=htail

end FCAppendix.Affine.Uniform07Finishing.Concrete05
