import FCAppendix.Affine.Uniform07Finishing.Native.Concrete05Adapter

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing.Concrete05
open MeasureTheory ProbabilityTheory Game Bayes Set Classical
open FCAppendix.Affine
open scoped BigOperators

theorem clip01_eq_min_max (x : ℝ) :
    max 0 (min 1 x)=min 1 (max 0 x) := by
  by_cases hx : x≤ 0
  · simp only [min_eq_right (hx.trans zero_le_one),max_eq_left hx,
      min_eq_right zero_le_one]
  · have hx0 : 0≤ x := (lt_of_not_ge hx).le
    by_cases hx1 : x≤ 1
    · simp only [min_eq_right hx1,max_eq_right hx0]
    · have h1x : 1≤ x := (lt_of_not_ge hx1).le
      simp only [min_eq_left h1x,max_eq_right hx0,max_eq_right zero_le_one]

theorem sourceRamp_normalization {ε M : ℝ} (hε : 0<ε) (hM : 0< M)
    (x : ℝ) :
    UniformFinite.Literal.ramp ((x/M-ε)/(2*ε-ε))=
      Weighted.sourceRamp (ε*M) x := by
  have hq : (x/M-ε)/(2*ε-ε)=(x-ε*M)/(ε*M) := by
    field_simp [hε.ne',hM.ne']
    ring
  rw [hq]
  exact clip01_eq_min_max _

theorem count_slack_normalization {M : ℝ} (hM : 0< M)
    (ε a b : ℝ) :
    10*ε-|a/M-b|=(10*ε*M-|a-b*M|)/M := by
  have hq : a/M-b=(a-b*M)/M := by
    field_simp [hM.ne']
  rw [hq,abs_div,abs_of_pos hM]
  field_simp [hM.ne']

section Context
variable {m : ℕ}

theorem decoded_lower (X : StrictNative.ClassifiedContext m) :
    (UniformFinite.NativeContext.decode X).lower=Weighted.presentSet X.1 := rfl

theorem decoded_upper (X : StrictNative.ClassifiedContext m)
    (hX : UniformFinite.NativeContext.Valid X) (j : Fin 2) :
    UniformFinite.Source.upperCount (UniformFinite.NativeContext.decode X) j=
      StrictNative.contextUpper j X :=
  UniformFinite.NativeContext.decode_upper X hX j

theorem decoded_residual (X : StrictNative.ClassifiedContext m)
    (hX : UniformFinite.NativeContext.Valid X) (j : Fin 2) :
    UniformFinite.Source.residual (UniformFinite.NativeContext.decode X) j=
      Weighted.budget (Uniform07.capacity m) j X := by
  rw [UniformFinite.Source.residual,decoded_lower,decoded_upper X hX j]
  exact min_comm _ _

theorem decoded_small (X : StrictNative.ClassifiedContext m)
    (hX : UniformFinite.NativeContext.Valid X) :
    UniformFinite.Source.small (UniformFinite.NativeContext.decode X)=
      Weighted.commonBudget (Uniform07.capacity m) X := by
  simp only [UniformFinite.Source.small,Weighted.commonBudget,decoded_residual X hX]

theorem decoded_imbalance (X : StrictNative.ClassifiedContext m)
    (hX : UniformFinite.NativeContext.Valid X) :
    UniformFinite.Source.imbalance (UniformFinite.NativeContext.decode X)=
      max (Weighted.budget (Uniform07.capacity m) 0 X)
        (Weighted.budget (Uniform07.capacity m) 1 X)-
          Weighted.commonBudget (Uniform07.capacity m) X := by
  simp only [UniformFinite.Source.imbalance,UniformFinite.Source.large,
    decoded_residual X hX,decoded_small X hX]

theorem decoded_lowerBids (X : StrictNative.ClassifiedContext m) :
    UniformFinite.Source.lowerBids (UniformFinite.NativeContext.decode X)
      (fun a=>entryBid (X.1 a))=(fun a=>entryBid (X.1 a)) := by
  funext a
  cases h : X.1 a with
  | none => simp [UniformFinite.Source.lowerBids,UniformFinite.NativeContext.decode,
      UniformFinite.NativeContext.present,h,entryBid]
  | some b => simp [UniformFinite.Source.lowerBids,UniformFinite.NativeContext.decode,
      UniformFinite.NativeContext.present,h,entryBid]

theorem decoded_sourceWeights (row : Uniform07.Row) (G : Uniform05.RestrictedLaw row)
    (X : StrictNative.ClassifiedContext m)
    (hU : ∀a,entryBid (X.1 a)≤ Early.bidCap row) :
    UniformFinite.Source.sourceWeights row G (UniformFinite.NativeContext.decode X)
      (fun a=>entryBid (X.1 a))=
      Weighted.sourceWeights (Uniform07.xi row) G.multiplier
        (Early.demandRatio row) (Early.bidCap row) X.1 := by
  apply Subtype.ext
  funext a
  cases h : X.1 a with
  | none => simp [UniformFinite.Source.sourceWeights,UniformFinite.NativeContext.decode,
      UniformFinite.NativeContext.present,Weighted.sourceWeights,Weighted.eligibleWeight,h]
  | some b =>
    have hb : b≤ Early.bidCap row := by simpa only [h,entryBid] using hU a
    simp only [UniformFinite.Source.sourceWeights,UniformFinite.NativeContext.decode,
      UniformFinite.NativeContext.present,Finset.mem_filter,Finset.mem_univ,
      h,entryBid,
      Uniform05.lawWeight,Uniform05.guardWeight,Uniform05.clip01,
      Uniform05.xi_eq_canonical,demand_eq,Weighted.sourceWeights,
      Weighted.eligibleWeight,if_pos hb,Weighted.guardWeight]
    exact clip01_eq_min_max _

theorem decoded_lowDemand (row : Uniform07.Row) (G : Uniform05.RestrictedLaw row)
    (X : StrictNative.ClassifiedContext m) :
    UniformFinite.Source.lowDemand row G (UniformFinite.NativeContext.decode X)
      (fun a=>entryBid (X.1 a))=
      Weighted.sourceDemand (Uniform07.xi row)
        (G.multiplier-Early.nativeRadius row) X.1 := by
  simp only [UniformFinite.Source.lowDemand,decoded_lowerBids,
    UniformFinite.Source.rootLo,guardRadius_eq_nativeRadius,
    Uniform05.xi_eq_canonical,Weighted.sourceDemand]

theorem decoded_highDemand (row : Uniform07.Row) (G : Uniform05.RestrictedLaw row)
    (X : StrictNative.ClassifiedContext m) :
    UniformFinite.Source.highDemand row G (UniformFinite.NativeContext.decode X)
      (fun a=>entryBid (X.1 a))=
      Weighted.sourceDemand (Uniform07.xi row)
        (G.multiplier+Early.nativeRadius row) X.1 := by
  simp only [UniformFinite.Source.highDemand,decoded_lowerBids,
    UniformFinite.Source.rootHi,guardRadius_eq_nativeRadius,
    Uniform05.xi_eq_canonical,Weighted.sourceDemand]

theorem decoded_rejectionSum (row : Uniform07.Row) (G : Uniform05.RestrictedLaw row)
    (X : StrictNative.ClassifiedContext m) :
    UniformFinite.Source.rejectionSum row G (UniformFinite.NativeContext.decode X)
      (fun a=>entryBid (X.1 a))=
      Weighted.sourceRejectionDemand (Uniform07.cutoff row/1000) G.rejectionRoot X.1 := by
  simp only [UniformFinite.Source.rejectionSum,decoded_lowerBids,
    rejection_scale_eq,Uniform05.rejectionExposure,
    Weighted.sourceRejectionDemand,Weighted.sourcePsi]

theorem sourceSlacks_eq_sourcePolicySlacks (row : Uniform07.Row)
    (G : Uniform05.RestrictedLaw row) (hm : 0< m)
    (X : StrictNative.ClassifiedContext m)
    (hX : UniformFinite.NativeContext.Valid X)
    (hU : ∀a,entryBid (X.1 a)≤ Early.bidCap row) (k : Fin 7) :
    UniformFinite.Source.sourceSlacks row G (UniformFinite.NativeContext.decode X)
      (fun a=>entryBid (X.1 a)) k=
      Weighted.sourcePolicySlacks (Uniform07.xi row) G.multiplier
        (Early.nativeRadius row) (Early.demandRatio row) (Early.bidCap row)
        (Uniform07.cutoff row/1000) G.rejectionRoot (Uniform07.cutoff row)
        (10*UniformFinite.Source.commonGuardMargin row) (Uniform07.capacity m) X k/m := by
  have hmR : (0:ℝ)< m := by exact_mod_cast hm
  have hu0 : (UniformFinite.NativeContext.decode X).upper0=X.2.1 := by
    simpa only [UniformFinite.Source.upperCount,StrictNative.contextUpper,if_true] using
      decoded_upper X hX 0
  have hu1 : (UniformFinite.NativeContext.decode X).upper1=X.2.2 := by
    simpa only [UniformFinite.Source.upperCount,StrictNative.contextUpper,
      show (1:Fin 2)≠0 by decide,if_false] using decoded_upper X hX 1
  have hcL := count_slack_normalization hmR (UniformFinite.Source.commonGuardMargin row)
    ((Weighted.presentSet X.1).card:ℝ) (Uniform07.cutoff row)
  have hc0 := count_slack_normalization hmR (UniformFinite.Source.commonGuardMargin row)
    (X.2.1:ℝ) ((1-Uniform07.cutoff row)/2)
  have hc1 := count_slack_normalization hmR (UniformFinite.Source.commonGuardMargin row)
    (X.2.2:ℝ) ((1-Uniform07.cutoff row)/2)
  fin_cases k
  · change (UniformFinite.Source.lowDemand row G (UniformFinite.NativeContext.decode X) (fun a=>entryBid (X.1 a))-(UniformFinite.Source.small (UniformFinite.NativeContext.decode X):ℝ)-UniformFinite.Source.imbalance (UniformFinite.NativeContext.decode X))/m =
      (Weighted.sourceDemand (Uniform07.xi row) (G.multiplier-Early.nativeRadius row) X.1-(Weighted.commonBudget (Uniform07.capacity m) X:ℝ)-((max (Weighted.budget (Uniform07.capacity m) 0 X) (Weighted.budget (Uniform07.capacity m) 1 X)-Weighted.commonBudget (Uniform07.capacity m) X:ℕ):ℝ))/m
    rw [decoded_lowDemand,decoded_small X hX,decoded_imbalance X hX]
  · change ((UniformFinite.Source.small (UniformFinite.NativeContext.decode X):ℝ)-UniformFinite.Source.highDemand row G (UniformFinite.NativeContext.decode X) (fun a=>entryBid (X.1 a)))/m =
      ((Weighted.commonBudget (Uniform07.capacity m) X:ℝ)-Weighted.sourceDemand (Uniform07.xi row) (G.multiplier+Early.nativeRadius row) X.1)/m
    rw [decoded_highDemand,decoded_small X hX]
  · change (WeightedSampling.totalWeight (UniformFinite.Source.sourceWeights row G (UniformFinite.NativeContext.decode X) (fun a=>entryBid (X.1 a)))-UniformFinite.Source.imbalance (UniformFinite.NativeContext.decode X))/m =
      (WeightedSampling.totalWeight (Weighted.sourceWeights (Uniform07.xi row) G.multiplier (Early.demandRatio row) (Early.bidCap row) X.1)-((max (Weighted.budget (Uniform07.capacity m) 0 X) (Weighted.budget (Uniform07.capacity m) 1 X)-Weighted.commonBudget (Uniform07.capacity m) X:ℕ):ℝ))/m
    rw [decoded_sourceWeights row G X hU,decoded_imbalance X hX]
  · change (UniformFinite.Source.rejectionSum row G (UniformFinite.NativeContext.decode X) (fun a=>entryBid (X.1 a))-UniformFinite.Source.totalResidual (UniformFinite.NativeContext.decode X))/m =
      (Weighted.sourceRejectionDemand (Uniform07.cutoff row/1000) G.rejectionRoot X.1-(Weighted.budget (Uniform07.capacity m) 0 X:ℝ)-(Weighted.budget (Uniform07.capacity m) 1 X:ℝ))/m
    simp only [decoded_rejectionSum,UniformFinite.Source.totalResidual,decoded_residual X hX,Nat.cast_add]
    ring
  · change 10*UniformFinite.Source.commonGuardMargin row-|((UniformFinite.NativeContext.decode X).lower.card:ℝ)/m-Uniform05.t row| =
      (10*UniformFinite.Source.commonGuardMargin row*m-|((Weighted.presentSet X.1).card:ℝ)-Uniform07.cutoff row*m|)/m
    simpa only [decoded_lower,Uniform05.t_eq_canonical] using hcL
  · change 10*UniformFinite.Source.commonGuardMargin row-|((UniformFinite.NativeContext.decode X).upper0:ℝ)/m-(1-Uniform05.t row)/2| =
      (10*UniformFinite.Source.commonGuardMargin row*m-|(X.2.1:ℝ)-(1-Uniform07.cutoff row)*m/2|)/m
    rw [hu0,Uniform05.t_eq_canonical]
    convert hc0 using 1
    congr 1
    ring
  · change 10*UniformFinite.Source.commonGuardMargin row-|((UniformFinite.NativeContext.decode X).upper1:ℝ)/m-(1-Uniform05.t row)/2| =
      (10*UniformFinite.Source.commonGuardMargin row*m-|(X.2.2:ℝ)-(1-Uniform07.cutoff row)*m/2|)/m
    rw [hu1,Uniform05.t_eq_canonical]
    convert hc1 using 1
    congr 1
    ring

theorem rawAlpha_eq_sourceGuardAlpha (row : Uniform07.Row)
    (G : Uniform05.RestrictedLaw row) (hm : 0< m)
    (X : StrictNative.ClassifiedContext m)
    (hX : UniformFinite.NativeContext.Valid X)
    (hU : ∀a,entryBid (X.1 a)≤ Early.bidCap row) :
    UniformFinite.Source.rawAlpha row G (UniformFinite.NativeContext.decode X)
      (fun a=>entryBid (X.1 a))=
      (Weighted.sourceGuardAlpha (Uniform07.xi row) G.multiplier
        (Early.nativeRadius row) (Early.demandRatio row) (Early.bidCap row)
        (Uniform07.cutoff row/1000) G.rejectionRoot (Uniform07.cutoff row)
        (10*UniformFinite.Source.commonGuardMargin row)
        (UniformFinite.Source.commonGuardMargin row) (Uniform07.capacity m) X:ℝ) := by
  unfold UniformFinite.Source.rawAlpha UniformFinite.Literal.guardWeight
    Weighted.sourceGuardAlpha
  dsimp only [Subtype.coe_mk]
  apply Finset.prod_congr rfl
  intro k _
  rw [sourceSlacks_eq_sourcePolicySlacks row G hm X hX hU k]
  exact sourceRamp_normalization (UniformFinite.Source.common_guard_margin row)
    (by exact_mod_cast hm) _

end Context
end FCAppendix.Affine.Uniform07Finishing.Concrete05
