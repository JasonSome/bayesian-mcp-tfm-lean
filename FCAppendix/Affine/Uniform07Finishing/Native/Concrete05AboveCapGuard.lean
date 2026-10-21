import FCAppendix.Affine.Uniform07Finishing.Native.Concrete05Guard
import FCAppendix.Affine.Uniform07Finishing.Native.GuardedSeedErasure
import FCAppendix.Affine.UniformFinite.Late.RemoveCap

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing.Concrete05
open MeasureTheory ProbabilityTheory Game Bayes Set Filter Topology Classical
open FCAppendix.Affine
open scoped BigOperators

variable {M : ℕ} [Nonempty (Fin M)]

theorem native_cap_positive (i : Uniform07.Row) : 0< Early.bidCap i := by
  rw [←cap_eq]
  exact Uniform05.cap_pos i

def rowContext (row : UniformFinite.Source.CountRow M) (b : Fin M→ℝ) :
    StrictNative.ClassifiedContext M :=
  (fun a => if a∈row.lower then some (b a) else none,(row.upper0,row.upper1))

omit [Nonempty (Fin M)] in
@[simp] theorem rowContext_present (row : UniformFinite.Source.CountRow M)
    (b : Fin M→ℝ) : Weighted.presentSet (rowContext row b).1=row.lower := by
  ext a
  by_cases ha : a∈row.lower <;> simp [rowContext,Weighted.presentSet,ha]

omit [Nonempty (Fin M)] in
theorem rowContext_entry (row : UniformFinite.Source.CountRow M)
    (b : Fin M→ℝ) :
    (fun a => entryBid ((rowContext row b).1 a))=UniformFinite.Source.lowerBids row b := by
  funext a
  by_cases ha : a∈row.lower <;>
    simp [rowContext,UniformFinite.Source.lowerBids,ha,entryBid]

omit [Nonempty (Fin M)] in
theorem rowContext_valid (row : UniformFinite.Source.CountRow M) (b : Fin M→ℝ) :
    UniformFinite.NativeContext.Valid (rowContext row b) := by
  change (Weighted.presentSet (rowContext row b).1).card+row.upper0+row.upper1=M
  rw [rowContext_present]
  exact row.partition

omit [Nonempty (Fin M)] in
@[simp] theorem rowContext_decode (row : UniformFinite.Source.CountRow M)
    (b : Fin M→ℝ) : UniformFinite.NativeContext.decode (rowContext row b)=row := by
  apply (UniformFinite.NativeContext.countRow_eq_iff _ _).mpr
  have h0 : row.upper0≤ M-row.lower.card := by have h:=row.partition; omega
  have h1 : M-row.lower.card-row.upper0=row.upper1 := by have h:=row.partition; omega
  refine ⟨rowContext_present row b,?_,?_⟩
  · change min row.upper0 (M-(Weighted.presentSet (rowContext row b).1).card)=row.upper0
    rw [rowContext_present,Nat.min_eq_left h0]
  · change M-(Weighted.presentSet (rowContext row b).1).card-
      min row.upper0 (M-(Weighted.presentSet (rowContext row b).1).card)=row.upper1
    rw [rowContext_present,Nat.min_eq_left h0,h1]

omit [Nonempty (Fin M)] in

theorem sourceStatistic_control_slacks_eight (i : Uniform07.Row)
    (G : Uniform05.RestrictedLaw i) (x : Fin M→ UniformFinite.Source.Observation i)
    (hM : 0< M)
    (hc : |(Uniform07.capacity M:ℝ)/M-Uniform05.rho|≤ UniformFinite.Source.commonGuardMargin i)
    (hx : ∀k : Fin 8, |(∑a,UniformFinite.Source.sourceStatistic i G k (x a))/(M:ℝ)-
      UniformFinite.Source.sourceMean i G k|≤ UniformFinite.Source.commonGuardMargin i) :
    ∀k : Fin 7, 8*UniformFinite.Source.commonGuardMargin i≤
      UniformFinite.Source.sourceSlacks i G (UniformFinite.Source.observationCountRow i x)
        (fun a=>UniformFinite.Source.observationBid i (x a)) k := by
  let row:=UniformFinite.Source.observationCountRow i x
  let b:=fun a=>UniformFinite.Source.observationBid i (x a)
  have hs:=UniformFinite.Source.sourceStatistic_sum i G x
  have h0:=hx 0
  have h1:=hx 1
  have h2:=hx 2
  have h3:=hx 3
  have h4:=hx 4
  have h5:=hx 5
  have h6:=hx 6
  rw [congrFun hs 0] at h0
  rw [congrFun hs 1] at h1
  rw [congrFun hs 2] at h2
  rw [congrFun hs 3] at h3
  rw [congrFun hs 4] at h4
  rw [congrFun hs 5] at h5
  rw [congrFun hs 6] at h6
  change |UniformFinite.Source.lowDemand i G row b/(M:ℝ)-
    Uniform05.t i*Uniform05.lawDemand i G.bidLaw (UniformFinite.Source.rootLo i G)| ≤
      UniformFinite.Source.commonGuardMargin i at h0
  change |UniformFinite.Source.highDemand i G row b/(M:ℝ)-
    Uniform05.t i*Uniform05.lawDemand i G.bidLaw (UniformFinite.Source.rootHi i G)| ≤
      UniformFinite.Source.commonGuardMargin i at h1
  change |WeightedSampling.totalWeight (UniformFinite.Source.sourceWeights i G row b)/(M:ℝ)-
    Uniform05.t i*(∫ q : Uniform05.Bid i, Uniform05.lawWeight i G q ∂(G.bidLaw : Measure _))| ≤
      UniformFinite.Source.commonGuardMargin i at h2
  change |UniformFinite.Source.rejectionSum i G row b/(M:ℝ)-
    3*UniformFinite.Source.meanResidual i| ≤ UniformFinite.Source.commonGuardMargin i at h3
  have he:=UniformFinite.Source.common_guard_margin i
  have heb:=UniformFinite.Source.commonGuardMargin_bounds i
  have hcount:=UniformFinite.Source.count_control i row hM hc h4 h5 h6
  have hD:=Uniform05.shifted_lawDemand_slack i G
  have hDlo:=mul_le_mul_of_nonneg_left hD.1 (Uniform05.t_pos i).le
  have hDhi:=mul_le_mul_of_nonneg_left hD.2 (Uniform05.t_pos i).le
  have hW:=mul_le_mul_of_nonneg_left (Uniform05.mean_lawWeight_lower i G) (Uniform05.t_pos i).le
  have hDlo' : UniformFinite.Source.meanResidual i+UniformFinite.Source.demandMargin i≤
      Uniform05.t i*Uniform05.lawDemand i G.bidLaw (UniformFinite.Source.rootLo i G) := by
    simpa only [UniformFinite.Source.meanResidual,UniformFinite.Source.demandMargin,
      UniformFinite.Source.rootLo,mul_add] using hDlo
  have hDhi' : Uniform05.t i*Uniform05.lawDemand i G.bidLaw (UniformFinite.Source.rootHi i G)≤
      UniformFinite.Source.meanResidual i-UniformFinite.Source.demandMargin i := by
    simpa only [UniformFinite.Source.meanResidual,UniformFinite.Source.demandMargin,
      UniformFinite.Source.rootHi,mul_sub] using hDhi
  change UniformFinite.Source.weightMargin i≤ _ at hW
  obtain ⟨hloL,hloR⟩:=abs_le.mp h0
  obtain ⟨hhiL,hhiR⟩:=abs_le.mp h1
  obtain ⟨hwL,hwR⟩:=abs_le.mp h2
  obtain ⟨hzL,hzR⟩:=abs_le.mp h3
  intro k
  fin_cases k
  · change 8*UniformFinite.Source.commonGuardMargin i ≤
      (UniformFinite.Source.lowDemand i G row b-(UniformFinite.Source.small row:ℝ)-
        UniformFinite.Source.imbalance row)/M
    have hsum : ((UniformFinite.Source.small row:ℝ)+UniformFinite.Source.imbalance row)/M=
        (UniformFinite.Source.large row:ℝ)/M := by
      rw [←Nat.cast_add,UniformFinite.Source.small_add_imbalance]
    rw [show UniformFinite.Source.lowDemand i G row b-(UniformFinite.Source.small row:ℝ)-
        UniformFinite.Source.imbalance row = UniformFinite.Source.lowDemand i G row b-
          ((UniformFinite.Source.small row:ℝ)+UniformFinite.Source.imbalance row) by ring,
      sub_div,hsum]
    linarith
  · change 8*UniformFinite.Source.commonGuardMargin i ≤
      ((UniformFinite.Source.small row:ℝ)-UniformFinite.Source.highDemand i G row b)/M
    rw [sub_div]
    linarith
  · change 8*UniformFinite.Source.commonGuardMargin i ≤
      (WeightedSampling.totalWeight (UniformFinite.Source.sourceWeights i G row b)-
        UniformFinite.Source.imbalance row)/M
    rw [sub_div]
    linarith
  · change 8*UniformFinite.Source.commonGuardMargin i ≤
      (UniformFinite.Source.rejectionSum i G row b-UniformFinite.Source.totalResidual row)/M
    rw [sub_div]
    linarith
  · change 8*UniformFinite.Source.commonGuardMargin i ≤
      10*UniformFinite.Source.commonGuardMargin i-|(row.lower.card:ℝ)/M-Uniform05.t i|
    change |(row.lower.card:ℝ)/M-Uniform05.t i| ≤ UniformFinite.Source.commonGuardMargin i at h4
    linarith
  · change 8*UniformFinite.Source.commonGuardMargin i ≤
      10*UniformFinite.Source.commonGuardMargin i-|(row.upper0:ℝ)/M-(1-Uniform05.t i)/2|
    change |(row.upper0:ℝ)/M-(1-Uniform05.t i)/2| ≤ UniformFinite.Source.commonGuardMargin i at h5
    linarith
  · change 8*UniformFinite.Source.commonGuardMargin i ≤
      10*UniformFinite.Source.commonGuardMargin i-|(row.upper1:ℝ)/M-(1-Uniform05.t i)/2|
    change |(row.upper1:ℝ)/M-(1-Uniform05.t i)/2| ≤ UniformFinite.Source.commonGuardMargin i at h6
    linarith

omit [Nonempty (Fin M)] in
theorem sum_unit_change_le (f g : Fin M→ℝ) (a : Fin M)
    (hfg : ∀j, j≠a → f j=g j) (hf : f a≤ 1) (hg : 0≤ g a) :
    (∑j,f j)≤(∑j,g j)+1 := by
  have hpoint (j : Fin M) : f j≤ g j+if j=a then 1 else 0 := by
    by_cases hj : j=a
    · subst j
      simp only [ite_true]
      linarith
    · simp only [hfg j hj,if_neg hj,add_zero,le_refl]
  have h:=Finset.sum_le_sum (s := Finset.univ) (fun j _=>hpoint j)
  simpa [Finset.sum_add_distrib] using h

omit [Nonempty (Fin M)] in

theorem sourcePolicySlacks_loss_one (i : Uniform07.Row) {Λ z width : ℝ}
    (hΛ : (54/100:ℝ)*Uniform07.cutoff i<Λ)
    (X Y : StrictNative.ClassifiedContext M) (a : Fin M)
    (hpres : Weighted.presentSet X.1=Weighted.presentSet Y.1) (hup : X.2=Y.2)
    (hrest : ∀j, j≠a → X.1 j=Y.1 j)
    (hw : Weighted.sourceWeights (Uniform07.xi i) Λ (Early.demandRatio i) (Early.bidCap i) X.1=
      Weighted.sourceWeights (Uniform07.xi i) Λ (Early.demandRatio i) (Early.bidCap i) Y.1) :
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
  have hcommon : Weighted.commonBudget (Uniform07.capacity M) X =
      Weighted.commonBudget (Uniform07.capacity M) Y := by
    simp only [Weighted.commonBudget,hb]
  have hdelta : (max (Weighted.budget (Uniform07.capacity M) 0 X)
      (Weighted.budget (Uniform07.capacity M) 1 X)-Weighted.commonBudget (Uniform07.capacity M) X) =
      (max (Weighted.budget (Uniform07.capacity M) 0 Y)
      (Weighted.budget (Uniform07.capacity M) 1 Y)-Weighted.commonBudget (Uniform07.capacity M) Y) := by
    rw [hb 0,hb 1,hcommon]
  intro k
  fin_cases k
  · change Weighted.sourceDemand (Uniform07.xi i) (Λ-Early.nativeRadius i) X.1-
      (Weighted.commonBudget (Uniform07.capacity M) X:ℝ)-
      ((max (Weighted.budget (Uniform07.capacity M) 0 X) (Weighted.budget (Uniform07.capacity M) 1 X)-
        Weighted.commonBudget (Uniform07.capacity M) X:ℕ):ℝ)-1 ≤
      Weighted.sourceDemand (Uniform07.xi i) (Λ-Early.nativeRadius i) Y.1-
      (Weighted.commonBudget (Uniform07.capacity M) Y:ℝ)-
      ((max (Weighted.budget (Uniform07.capacity M) 0 Y) (Weighted.budget (Uniform07.capacity M) 1 Y)-
        Weighted.commonBudget (Uniform07.capacity M) Y:ℕ):ℝ)
    rw [hdelta,hcommon]
    dsimp only [Weighted.sourceDemand]
    linarith only [hLo]
  · change (Weighted.commonBudget (Uniform07.capacity M) X:ℝ)-
      Weighted.sourceDemand (Uniform07.xi i) (Λ+Early.nativeRadius i) X.1-1 ≤
      (Weighted.commonBudget (Uniform07.capacity M) Y:ℝ)-
      Weighted.sourceDemand (Uniform07.xi i) (Λ+Early.nativeRadius i) Y.1
    rw [hcommon]
    dsimp only [Weighted.sourceDemand]
    linarith only [hHi]
  · change WeightedSampling.totalWeight (Weighted.sourceWeights (Uniform07.xi i) Λ
      (Early.demandRatio i) (Early.bidCap i) X.1)-
      ((max (Weighted.budget (Uniform07.capacity M) 0 X) (Weighted.budget (Uniform07.capacity M) 1 X)-
        Weighted.commonBudget (Uniform07.capacity M) X:ℕ):ℝ)-1 ≤
      WeightedSampling.totalWeight (Weighted.sourceWeights (Uniform07.xi i) Λ
      (Early.demandRatio i) (Early.bidCap i) Y.1)-
      ((max (Weighted.budget (Uniform07.capacity M) 0 Y) (Weighted.budget (Uniform07.capacity M) 1 Y)-
        Weighted.commonBudget (Uniform07.capacity M) Y:ℕ):ℝ)
    rw [hw,hdelta]
    linarith
  · change Weighted.sourceRejectionDemand (Uniform07.cutoff i/1000) z X.1-
      (Weighted.budget (Uniform07.capacity M) 0 X:ℝ)-(Weighted.budget (Uniform07.capacity M) 1 X:ℝ)-1 ≤
      Weighted.sourceRejectionDemand (Uniform07.cutoff i/1000) z Y.1-
      (Weighted.budget (Uniform07.capacity M) 0 Y:ℝ)-(Weighted.budget (Uniform07.capacity M) 1 Y:ℝ)
    rw [hb 0,hb 1]
    dsimp only [Weighted.sourceRejectionDemand]
    linarith only [hZ]
  · change width*M-|((Weighted.presentSet X.1).card:ℝ)-Uniform07.cutoff i*M|-1 ≤
      width*M-|((Weighted.presentSet Y.1).card:ℝ)-Uniform07.cutoff i*M|
    rw [hpres]
    linarith
  · change width*M-|(X.2.1:ℝ)-(1-Uniform07.cutoff i)*M/2|-1 ≤
      width*M-|(Y.2.1:ℝ)-(1-Uniform07.cutoff i)*M/2|
    rw [congrArg Prod.fst hup]
    linarith
  · change width*M-|(X.2.2:ℝ)-(1-Uniform07.cutoff i)*M/2|-1 ≤
      width*M-|(Y.2.2:ℝ)-(1-Uniform07.cutoff i)*M/2|
    rw [congrArg Prod.snd hup]
    linarith

omit [Nonempty (Fin M)] in

theorem rowContext_outcap_weights (i : Uniform07.Row) (G : Uniform05.RestrictedLaw i)
    (row : UniformFinite.Source.CountRow M) (b : Fin M→ℝ) (a : Fin M)
    (ha : a∈row.lower) (hzero : b a=0) {own : ℝ} (hown : Early.bidCap i< own) :
    Weighted.sourceWeights (Uniform07.xi i) G.multiplier
      (Early.demandRatio i) (Early.bidCap i) (rowContext row b).1 =
    Weighted.sourceWeights (Uniform07.xi i) G.multiplier
      (Early.demandRatio i) (Early.bidCap i) (rowContext row (Function.update b a own)).1 := by
  apply Subtype.ext
  funext j
  by_cases hj : j=a
  · subst j
    have hG : 0< G.multiplier := (Uniform05.demandLo_pos i).trans G.multiplier_guards.1
    have hz : ClippedResidual.exposure (Uniform07.xi i) G.multiplier 0=0 :=
      ClippedResidual.exposure_zero hG.le
    simp only [Weighted.sourceWeights,rowContext,if_pos ha,Weighted.eligibleWeight,
      hzero,Function.update_self,if_neg (not_le.mpr hown),
      if_pos (native_cap_positive i).le,hz,
      Weighted.guardWeight_zero (Early.demandRatio_pos i)
        (div_nonneg (Early.demandRatio_pos i).le (by norm_num))]
  · simp only [Weighted.sourceWeights,rowContext,Function.update_of_ne hj]

omit [Nonempty (Fin M)] in

theorem native_alpha_one_of_source_control (i : Uniform07.Row)
    (G : Uniform05.RestrictedLaw i) (x : Fin M→ UniformFinite.Source.Observation i)
    (a : Fin M) (ha : a∈(UniformFinite.Source.observationCountRow i x).lower)
    (hzero : UniformFinite.Source.observationBid i (x a)=0) (hM : 0< M)
    (hc : |(Uniform07.capacity M:ℝ)/M-Uniform05.rho|≤ UniformFinite.Source.commonGuardMargin i)
    (hx : ∀k : Fin 8, |(∑j,UniformFinite.Source.sourceStatistic i G k (x j))/(M:ℝ)-
      UniformFinite.Source.sourceMean i G k|≤ UniformFinite.Source.commonGuardMargin i)
    (hsize : 1≤ UniformFinite.Source.commonGuardMargin i*M)
    {own : ℝ} (hown : Early.bidCap i< own) :
    (literalSourceAlpha i G.multiplier G.rejectionRoot
      (10*UniformFinite.Source.commonGuardMargin i) (UniformFinite.Source.commonGuardMargin i)
      (rowContext (UniformFinite.Source.observationCountRow i x)
        (Function.update (fun j=>UniformFinite.Source.observationBid i (x j)) a own)) : ℝ)=1 := by
  let row:=UniformFinite.Source.observationCountRow i x
  let b:=fun j=>UniformFinite.Source.observationBid i (x j)
  let X:=rowContext row b
  let Y:=rowContext row (Function.update b a own)
  have hcap : ∀j,entryBid (X.1 j)≤ Early.bidCap i := by
    intro j
    have he : (fun j=>entryBid (X.1 j))=b := by
      simpa only [X,rowContext_entry] using UniformFinite.Source.lowerBids_observation i x
    rw [congrFun he j]
    simpa only [b,cap_eq] using UniformFinite.Source.observationBid_cap i (x j)
  have hΛ : (54/100:ℝ)*Uniform07.cutoff i< G.multiplier := by
    simpa only [Uniform05.t_eq_canonical] using G.multiplier_guards.1
  have hmargin:=sourceStatistic_control_slacks_eight i G x hM hc hx
  have hw:=rowContext_outcap_weights i G row b a ha hzero hown
  have hloss:=sourcePolicySlacks_loss_one i (z := G.rejectionRoot)
    (width := 10*UniformFinite.Source.commonGuardMargin i) hΛ X Y a
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
  change (∏k : Fin 7,Weighted.sourceRamp (UniformFinite.Source.commonGuardMargin i*M)
    (Weighted.sourcePolicySlacks (Uniform07.xi i) G.multiplier (Early.nativeRadius i)
      (Early.demandRatio i) (Early.bidCap i) (Uniform07.cutoff i/1000) G.rejectionRoot
      (Uniform07.cutoff i) (10*UniformFinite.Source.commonGuardMargin i)
      (Uniform07.capacity M) Y k))=1
  have hone (k : Fin 7) := Weighted.sourceRamp_one (mul_pos he hMr) (hinner k)
  simp only [hone,Finset.prod_const_one]

theorem observation_bid_bounds (i : Uniform07.Row)
    (x : UniformFinite.Source.Observation i) :
    UniformFinite.Source.observationBid i x∈Icc (0:ℝ) (Early.bidCap i) := by
  cases x with
  | inl p =>
    change (p.2 : ℝ) ∈ Icc 0 (Early.bidCap i)
    rw [←cap_eq]
    exact p.2.property
  | inr j => exact ⟨le_rfl,(native_cap_positive i).le⟩

omit [Nonempty (Fin M)] in

theorem rowContext_update_entry [NeZero M]
    (row : UniformFinite.Source.CountRow M) (b : Fin M→ℝ) (a : Fin M)
    (ha : a∈row.lower) (hmask : UniformFinite.Source.lowerBids row b=b) (own : ℝ) :
    (fun j=>entryBid ((rowContext row (Function.update b a own)).1 j))=
      Function.update b a own := by
  rw [rowContext_entry,UniformFinite.Late.Exceptional.lowerBids_update row b a ha own,hmask]

omit [Nonempty (Fin M)] in

theorem rowContext_exceptional_weight [NeZero M]
    (i : Uniform07.Row) (G : Uniform05.RestrictedLaw i)
    (row : UniformFinite.Source.CountRow M) (b : Fin M→ℝ) (a : Fin M)
    (ha : a∈row.lower) (hmask : UniformFinite.Source.lowerBids row b=b)
    (hzero : b a=0) (hcap : ∀j,b j≤ Early.bidCap i)
    {own : ℝ} (hown : Early.bidCap i< own) :
    UniformFinite.Late.Exceptional.weight i G
      (UniformFinite.NativeContext.decode (rowContext row (Function.update b a own)))
      (fun j=>entryBid ((rowContext row (Function.update b a own)).1 j)) a=
      Weighted.sourceWeights (Uniform07.xi i) G.multiplier
        (Early.demandRatio i) (Early.bidCap i)
        (rowContext row (Function.update b a own)).1 := by
  have hbase : ∀j,entryBid ((rowContext row b).1 j)≤ Early.bidCap i := by
    intro j
    have he : (fun j=>entryBid ((rowContext row b).1 j))=b := by
      rw [rowContext_entry,hmask]
    rw [congrFun he j]
    exact hcap j
  have hw:=decoded_sourceWeights i G (rowContext row b) hbase
  rw [rowContext_decode,rowContext_entry,hmask] at hw
  rw [rowContext_decode,rowContext_update_entry row b a ha hmask own,
    UniformFinite.Late.Exceptional.weight,
    UniformFinite.Late.Exceptional.ordinary_update row b a ha hmask hzero own,
    hw,rowContext_outcap_weights i G row b a ha hzero hown]

omit [Nonempty (Fin M)] in

theorem source_menu_seedCount_gt_one [NeZero M]
    (i : Uniform07.Row) (G : Uniform05.RestrictedLaw i)
    (x : Fin M→ UniformFinite.Source.Observation i) {δ : ℝ}
    (hδ : δ≤ UniformFinite.Source.commonGuardMargin i)
    (hsize : 4/(M:ℝ)≤δ) (hx : UniformFinite.Source.MenuGood i G δ x) :
    1< UniformFinite.Source.seedCount i (UniformFinite.Source.observationCountRow i x)
      (fun j=>UniformFinite.Source.observationBid i (x j)) := by
  have hM : 0< M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hMr : (0:ℝ)< M := by exact_mod_cast hM
  have hinv : 1/(M:ℝ)≤δ :=
    (div_le_div_of_nonneg_right (by norm_num : (1:ℝ)≤ 4) hMr.le).trans hsize
  have h7:=(hx.1 7).le
  rw [congrFun (UniformFinite.Source.sourceStatistic_sum i G x) 7] at h7
  change |(UniformFinite.Source.seedCount i (UniformFinite.Source.observationCountRow i x)
    (fun j=>UniformFinite.Source.observationBid i (x j)):ℝ)/M-
    UniformFinite.Source.sourceMean i G 7| ≤ δ at h7
  have hm:=(UniformFinite.Source.sourceMean_guard_bounds i G).2.2.2.2
  have he:=UniformFinite.Source.count_margin i
  have hl:=(abs_le.mp h7).1
  have hδt : δ< Uniform05.t i/200 := hδ.trans_lt he
  have hrate : 1/(M:ℝ)<
      (UniformFinite.Source.seedCount i (UniformFinite.Source.observationCountRow i x)
        (fun j=>UniformFinite.Source.observationBid i (x j)):ℝ)/M := by
    have ht:=Uniform05.t_pos i
    linarith
  have hh:=(div_lt_div_iff_of_pos_right hMr).mp hrate
  exact_mod_cast hh

omit [Nonempty (Fin M)] in
theorem rival_seed_of_seedCount_gt_one (i : Uniform07.Row)
    (row : UniformFinite.Source.CountRow M) (b : Fin M→ℝ) (a : Fin M)
    (hseed : 1< UniformFinite.Source.seedCount i row b) :
    ∃j,j≠a ∧ j∈row.lower ∧ b j≤ Uniform05.t i/2 := by
  classical
  by_contra hn
  have hsub : row.lower.filter (fun j=>b j≤ Uniform05.t i/2)⊆{a} := by
    intro j hj
    have hm:=Finset.mem_filter.mp hj
    apply Finset.mem_singleton.mpr
    by_contra hja
    exact hn ⟨j,hja,hm.1,hm.2⟩
  have hc:=Finset.card_le_card hsub
  simp only [Finset.card_singleton] at hc
  exact (not_le.mpr hseed) hc

omit [Nonempty (Fin M)] in

theorem both_alphas_one_of_menu [NeZero M]
    (i : Uniform07.Row) (G : Uniform05.RestrictedLaw i)
    (x : Fin M→ UniformFinite.Source.Observation i) (a : Fin M)
    (ha : a∈(UniformFinite.Source.observationCountRow i x).lower)
    (hzero : UniformFinite.Source.observationBid i (x a)=0)
    {own δ : ℝ} (hown : Early.bidCap i< own) (hownT : own≤ Uniform05.t i)
    (hreceipt : Uniform05.kappa i*Uniform05.t i≤ UniformFinite.Source.rootLo i G)
    (hδ : δ≤ UniformFinite.Source.commonGuardMargin i)
    (hsize : 4/(M:ℝ)≤δ)
    (hc : |(Uniform07.capacity M:ℝ)/M-Uniform05.rho|≤δ)
    (hx : UniformFinite.Source.MenuGood i G δ x) :
    let row:=UniformFinite.Source.observationCountRow i x
    let b:=fun j=>UniformFinite.Source.observationBid i (x j)
    (literalSourceAlpha i G.multiplier G.rejectionRoot
      (10*UniformFinite.Source.commonGuardMargin i) (UniformFinite.Source.commonGuardMargin i)
      (rowContext row (Function.update b a own)):ℝ)=1 ∧
    UniformFinite.Late.Exceptional.alpha i G row (Function.update b a own) a=1 ∧
    ∃j,j≠a ∧ j∈row.lower ∧ b j≤ Uniform05.t i/2 := by
  dsimp only
  have hM : 0< M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hMr : (0:ℝ)< M := by exact_mod_cast hM
  have h4 : (4:ℝ)≤δ*M := (div_le_iff₀ hMr).mp hsize
  have hscale:=mul_le_mul_of_nonneg_right hδ hMr.le
  have hroom : 2< UniformFinite.Source.commonGuardMargin i*M := by linarith
  have hseed:=source_menu_seedCount_gt_one i G x hδ hsize hx
  have hguard:=UniformFinite.Source.sourceStatistic_control_guardAlpha_one i G x hM
    (hc.trans hδ) (fun k=>(hx.1 k).le.trans hδ)
  refine ⟨native_alpha_one_of_source_control i G x a ha hzero hM
    (hc.trans hδ) (fun k=>(hx.1 k).le.trans hδ) (by linarith) hown,?_,
    rival_seed_of_seedCount_gt_one i _ _ a hseed⟩
  exact UniformFinite.Late.Exceptional.alpha_one_of_control i G _ _ a ha
    (UniformFinite.Source.lowerBids_observation i x) hzero hownT hreceipt hroom hseed hguard

end FCAppendix.Affine.Uniform07Finishing.Concrete05
