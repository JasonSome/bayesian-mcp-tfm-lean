import FCAppendix.Affine.Tail04.NativeFocalVector
import FCAppendix.Affine.Tail04.NativeKernelIntegration

noncomputable section
namespace FCAppendix.Affine.Tail04.NativeCompatibleMeans
open MeasureTheory ProbabilityTheory Set Classical Filter Game Bayes
open LocalCoordinates SortedCoordinates NativeLocalPolicy NativeObservationPair NativePolicyFactor
open NativeRawFactor NativeFocalFactor NativeFocalVector NativeKernelIntegration
open JoinedHighPolicy EqualPrivateSignal EqualPrivateUpper Hybrid

variable {m c : ℕ} (D : Data m c) (Γ : FiniteGame m 2 c Seed)
    (κ : Fin 2 → Kernel (LocalList m) (UserProfile m 2)) [∀ j,IsMarkovKernel (κ j)]
    (hseed : Γ.seedLaw=seedLaw) (hpolicy : ∀ j,Γ.policy j=D.completedPolicy j)
    (j : Fin 2) (L : LocalList m)
    (hc : ∀ᵐ d ∂κ j L,D.E.Compatible L (observe (drawsRealization d) (otherProposer j)))
    (hr : (κ j L).map (fun d => privateRow D.E (ids D.E 3 L)
      (observe (drawsRealization d) (otherProposer j)))=
      (D.originalPrivateRow (D.finiteCount (ids D.E 3 L)) : Measure (Row (D.finiteCount (ids D.E 3 L)).val D.E.R D.E.Rp D.E.H)))

local instance : PolishSpace (Ici D.E.H) := isClosed_Ici.polishSpace
local instance : PolishSpace (Icc D.E.R D.E.Rp) := isClosed_Icc.polishSpace

lemma measurable_missing_row : Measurable (fun d : UserProfile m 2 => privateRow D.E (ids D.E 3 L)
    (observe (drawsRealization d) (otherProposer j))) :=
  (measurable_privateRow D.E _).comp (measurable_observe_draws _)

include hpolicy hc in
theorem private_mean (i : Fin m) (hi : D.E.localTag (L i)=2) :
    otherMean Γ κ j L i=0 := by
  apply zero_mean Γ κ j L i
  filter_upwards [hc] with d hd
  intro u
  rw [hpolicy (otherProposer j)]
  exact (NativePolicyFactor.opposite_private_absent D) hd j i hi u

include hseed hpolicy hc hr in
theorem onMenu_active (hm : D.offCommon L=∅) (i : Fin m) (hi : i∈ids D.E 1 L) :
    otherMean Γ κ j L i=D.oppositeActiveMean j L
      (rankFin (ids D.E 1 L) (bidVector L) ⟨i,hi⟩) := by
  have hj : j=0 ∨ j=1 := by omega
  rcases hj with rfl | rfl
  · rw [(NativePolicyFactor.oppositeActiveMean_zero D),Data.zeroMean]
    apply sampler_mean Γ κ hseed 0 L i
      (D.oneSampler (ids D.E 1 L).card (D.finiteCount (ids D.E 2 L)) (D.finiteCount (ids D.E 3 L)))
      (D.oneSampler_measurable _ _ _) _ _ (measurable_missing_row D 0 L)
      (D.originalPrivateRow (D.finiteCount (ids D.E 3 L)) : Measure (Row (D.finiteCount (ids D.E 3 L)).val D.E.R D.E.Rp D.E.H)) hr _
    filter_upwards [hc] with d hd
    intro u
    rw [hpolicy (otherProposer 0),D.completed_on_menu (otherProposer 0) _
      (by rw [←(NativeRawFactor.offCommon_pair D) hd];exact hm) u]
    simpa only [otherProposer,ite_true] using (NativePolicyFactor.opposite_one_factor D) hd i hi u
  · rw [(NativePolicyFactor.oppositeActiveMean_one D),Data.oneMean]
    apply sampler_mean Γ κ hseed 1 L i
      (D.zeroSampler (ids D.E 1 L).card (D.finiteCount (ids D.E 3 L)) (D.finiteCount (ids D.E 2 L)))
      (D.zeroSampler_measurable _ _ _) _ _ (measurable_missing_row D 1 L)
      (D.originalPrivateRow (D.finiteCount (ids D.E 3 L)) : Measure (Row (D.finiteCount (ids D.E 3 L)).val D.E.R D.E.Rp D.E.H)) hr _
    filter_upwards [hc] with d hd
    intro u
    rw [hpolicy (otherProposer 1),D.completed_on_menu (otherProposer 1) _
      (by rw [←(NativeRawFactor.offCommon_pair D) hd];exact hm) u]
    simpa only [otherProposer,if_neg (by decide : (1:Fin 2)≠0)] using (NativePolicyFactor.opposite_zero_factor D) hd i hi u

include hseed hpolicy hc in
theorem onMenu_low (hm : D.offCommon L=∅) (i : Fin m) (hi : D.E.localTag (L i)=0) :
    otherMean Γ κ j L i=NativeExactLow.acceptance D.ξ D.xi_pos D.xi_lt_one c
      (otherProposer j) (Observable.Regions.lowContext D.E j L) i := by
  apply low_mean Γ κ hseed D j L i
  filter_upwards [hc] with d hd
  intro u
  rw [hpolicy (otherProposer j),D.completed_on_menu (otherProposer j) _
    (by rw [←(NativeRawFactor.offCommon_pair D) hd];exact hm) u]
  exact (NativePolicyFactor.opposite_low_factor D) hd j i hi u

include hseed hpolicy hc hr in
theorem raw_mean (hOff : D.offCommon L≠∅) (hf : ∀ f,¬D.UseFocal j f L)
    (i : Fin m) (hi : i∈D.rawCommon L) :
    otherMean Γ κ j L i=D.rawOppositeMean j L
      (rankFin (D.rawCommon L) (bidVector L) ⟨i,hi⟩) := by
  have hj : j=0 ∨ j=1 := by omega
  rcases hj with rfl | rfl
  · rw [(NativeRawFactor.rawOppositeMean_zero D)]
    erw [←D.rawMean1_original (D.rawCommon L)
      (D.finiteCount (ids D.E 2 L)) (D.finiteCount (ids D.E 3 L)) L]
    apply sampler_mean Γ κ hseed 0 L i
      (PairedRawPolicy.one (D.rawCommon L).card (D.finiteCount (ids D.E 2 L)).val (D.finiteCount (ids D.E 3 L)).val
        c D.E.R D.E.Rp D.E.H D.ξ)
      (PairedRawPolicy.measurable_one _ _ _ _ _ _ _ _) _ _
      (measurable_missing_row D 0 L)
      (D.originalPrivateRow (D.finiteCount (ids D.E 3 L)) : Measure (Row (D.finiteCount (ids D.E 3 L)).val D.E.R D.E.Rp D.E.H)) hr _
    filter_upwards [hc] with d hd
    intro u
    rw [hpolicy (otherProposer 0),(NativeRawFactor.fallback_pair D) hd 0 hOff hf u]
    have hh := (NativeRawFactor.opposite_raw_one D) hd i hi u
    simp only [otherProposer,ite_true,Data.finiteCount] at hh ⊢
    convert! hh using 1
  · rw [(NativeRawFactor.rawOppositeMean_one D)]
    erw [←D.rawMean0_original (D.rawCommon L)
      (D.finiteCount (ids D.E 3 L)) (D.finiteCount (ids D.E 2 L)) L]
    apply sampler_mean Γ κ hseed 1 L i
      (PairedRawPolicy.zero (D.rawCommon L).card (D.finiteCount (ids D.E 3 L)).val (D.finiteCount (ids D.E 2 L)).val
        c D.E.R D.E.Rp D.E.H D.ξ)
      (PairedRawPolicy.measurable_zero _ _ _ _ _ _ _ _) _ _
      (measurable_missing_row D 1 L)
      (D.originalPrivateRow (D.finiteCount (ids D.E 3 L)) : Measure (Row (D.finiteCount (ids D.E 3 L)).val D.E.R D.E.Rp D.E.H)) hr _
    filter_upwards [hc] with d hd
    intro u
    rw [hpolicy (otherProposer 1),(NativeRawFactor.fallback_pair D) hd 1 hOff hf u]
    have hh := (NativeRawFactor.opposite_raw_zero D) hd i hi u
    simp only [otherProposer,if_neg (by decide : (1:Fin 2)≠0),Data.finiteCount] at hh ⊢
    convert! hh using 1

include hseed hpolicy hc hr in
theorem focal_mean (f : Fin m) (hf : D.UseFocal j f L)
    (x : Option (Fin ((ids D.E 1 L).erase f).card)) :
    otherMean Γ κ j L (commonIdentity f ((ids D.E 1 L).erase f) (bidVector L) x)=
      (NativeFocalFactor.focalOppositeMean D) j f L x := by
  have hj : j=0 ∨ j=1 := by omega
  rcases hj with rfl | rfl
  · simp only [focalOppositeMean,ite_true]
    rw [←(NativeFocalFactor.focalCommonMean1_original D) _ _ _ _ _ ((NativeFocalFactor.FocalUse_zero D) f L hf)]
    apply sampler_mean Γ κ hseed 0 L _
      (D.oneFocal ((ids D.E 1 L).erase f).card (D.finiteCount (ids D.E 2 L))
        (D.finiteCount (ids D.E 3 L)))
      (D.measurable_oneFocal _ _ _) _ _ (measurable_missing_row D 0 L)
      (D.originalPrivateRow (D.finiteCount (ids D.E 3 L)) : Measure (Row (D.finiteCount (ids D.E 3 L)).val D.E.R D.E.Rp D.E.H)) hr _
    filter_upwards [hc] with d hd
    have hp : D.UseFocal (otherProposer 0) f (observe (drawsRealization d) (otherProposer 0)) :=
      ((NativeRawFactor.UseFocal_pair D) hd 0 f).mp hf
    intro u
    rw [hpolicy (otherProposer 0),D.completed_focal _ _ _ hp u]
    simpa only [otherProposer,ite_true] using (NativeFocalFactor.opposite_focal_one D) hd f hf x u
  · simp only [focalOppositeMean,if_neg (by decide : (1:Fin 2)≠0)]
    rw [←(NativeFocalFactor.focalCommonMean0_original D) _ _ _ _ _ ((NativeFocalFactor.FocalUse_one D) f L hf)]
    apply sampler_mean Γ κ hseed 1 L _
      (D.zeroFocal ((ids D.E 1 L).erase f).card (D.finiteCount (ids D.E 3 L))
        (D.finiteCount (ids D.E 2 L)))
      (D.measurable_zeroFocal _ _ _) _ _ (measurable_missing_row D 1 L)
      (D.originalPrivateRow (D.finiteCount (ids D.E 3 L)) : Measure (Row (D.finiteCount (ids D.E 3 L)).val D.E.R D.E.Rp D.E.H)) hr _
    filter_upwards [hc] with d hd
    have hp : D.UseFocal (otherProposer 1) f (observe (drawsRealization d) (otherProposer 1)) :=
      ((NativeRawFactor.UseFocal_pair D) hd 1 f).mp hf
    intro u
    rw [hpolicy (otherProposer 1),D.completed_focal _ _ _ hp u]
    simpa only [otherProposer,if_neg (by decide : (1:Fin 2)≠0)] using (NativeFocalFactor.opposite_focal_zero D) hd f hf x u

include hpolicy hc in
theorem focal_low (f : Fin m) (hf : D.UseFocal j f L)
    (i : Fin m) (hi : D.E.localTag (L i)=0) : otherMean Γ κ j L i=0 := by
  apply zero_mean Γ κ j L i
  filter_upwards [hc] with d hd
  have hp := ((NativeRawFactor.UseFocal_pair D) hd j f).mp hf
  have hit := (D.E.entry_common_tag (hd i) (Or.inl rfl)).mp hi
  intro u
  rw [hpolicy (otherProposer j),D.completed_focal _ _ _ hp u]
  exact (NativeFocalFactor.focal_low_absent D) _ _ _ hp i hit u

end FCAppendix.Affine.Tail04.NativeCompatibleMeans
