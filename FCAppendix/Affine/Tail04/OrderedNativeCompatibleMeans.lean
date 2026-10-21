import FCAppendix.Affine.Tail04.OrderedNativePolicy
import FCAppendix.Affine.Tail04.NativeFocalVector
import FCAppendix.Affine.Tail04.NativeKernelIntegration

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedNativeCompatibleMeans
open MeasureTheory ProbabilityTheory Set Classical Filter Game Bayes
open LocalCoordinates SortedCoordinates NativeLocalPolicy NativeObservationPair NativePolicyFactor
open NativeRawFactor NativeFocalFactor NativeFocalVector NativeKernelIntegration
open JoinedHighPolicy EqualPrivateSignal EqualPrivateUpper Hybrid

variable {m c : ℕ} (D : Data m c) (Γ : FiniteGame m 2 c Seed)
    (κ : Fin 2 → Kernel (LocalList m) (UserProfile m 2)) [∀ j,IsMarkovKernel (κ j)]
    (hseed : Γ.seedLaw=seedLaw) (hpolicy : ∀ j,Γ.policy j=OrderedNativePolicy.policy D j)
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

include hpolicy in
lemma policy_other_compatible {K : LocalList m} (h : D.E.Compatible L K) (u : Seed) :
    Γ.policy (otherProposer j) K u =
      D.completedPolicy (otherProposer (OrderedNativePolicy.role D.E j L)) K u := by
  rw [hpolicy,OrderedNativePolicy.policy,OrderedNativePolicy.role_pair D.E h j]

include hpolicy hc in
theorem private_mean (i : Fin m) (hi : D.E.localTag (L i)=2) :
    otherMean Γ κ j L i=0 := by
  apply zero_mean Γ κ j L i
  filter_upwards [hc] with d hd
  intro u
  rw [policy_other_compatible D Γ hpolicy j L hd u]
  exact (NativePolicyFactor.opposite_private_absent D) hd (OrderedNativePolicy.role D.E j L) i hi u

include hseed hpolicy hc hr in
theorem onMenu_active (hm : D.offCommon L=∅) (i : Fin m) (hi : i∈ids D.E 1 L) :
    otherMean Γ κ j L i=D.oppositeActiveMean (OrderedNativePolicy.role D.E j L) L
      (rankFin (ids D.E 1 L) (bidVector L) ⟨i,hi⟩) := by
  have hj : OrderedNativePolicy.role D.E j L=0 ∨ OrderedNativePolicy.role D.E j L=1 := by
    have hh := (OrderedNativePolicy.role D.E j L).isLt
    omega
  rcases hj with hj | hj
  · rw [hj,(NativePolicyFactor.oppositeActiveMean_zero D),Data.zeroMean]
    apply sampler_mean Γ κ hseed j L i
      (D.oneSampler (ids D.E 1 L).card (D.finiteCount (ids D.E 2 L)) (D.finiteCount (ids D.E 3 L)))
      (D.oneSampler_measurable _ _ _) _ _ (measurable_missing_row D j L)
      (D.originalPrivateRow (D.finiteCount (ids D.E 3 L)) : Measure (Row (D.finiteCount (ids D.E 3 L)).val D.E.R D.E.Rp D.E.H)) hr _
    filter_upwards [hc] with d hd
    intro u
    rw [policy_other_compatible D Γ hpolicy j L hd u,hj,D.completed_on_menu (otherProposer 0) _
      (by rw [←(NativeRawFactor.offCommon_pair D) hd];exact hm) u]
    simpa only [otherProposer,ite_true] using (NativePolicyFactor.opposite_one_factor D) hd i hi u
  · rw [hj,(NativePolicyFactor.oppositeActiveMean_one D),Data.oneMean]
    apply sampler_mean Γ κ hseed j L i
      (D.zeroSampler (ids D.E 1 L).card (D.finiteCount (ids D.E 3 L)) (D.finiteCount (ids D.E 2 L)))
      (D.zeroSampler_measurable _ _ _) _ _ (measurable_missing_row D j L)
      (D.originalPrivateRow (D.finiteCount (ids D.E 3 L)) : Measure (Row (D.finiteCount (ids D.E 3 L)).val D.E.R D.E.Rp D.E.H)) hr _
    filter_upwards [hc] with d hd
    intro u
    rw [policy_other_compatible D Γ hpolicy j L hd u,hj,D.completed_on_menu (otherProposer 1) _
      (by rw [←(NativeRawFactor.offCommon_pair D) hd];exact hm) u]
    simpa only [otherProposer,if_neg (by decide : (1:Fin 2)≠0)] using (NativePolicyFactor.opposite_zero_factor D) hd i hi u

include hseed hpolicy hc in
theorem onMenu_low (hm : D.offCommon L=∅) (i : Fin m) (hi : D.E.localTag (L i)=0) :
    otherMean Γ κ j L i=NativeExactLow.acceptance D.ξ D.xi_pos D.xi_lt_one c
      (otherProposer j) (Observable.Regions.lowContext D.E j L) i := by
  apply low_mean Γ κ hseed D j L i
  filter_upwards [hc] with d hd
  intro u
  rw [hpolicy (otherProposer j),OrderedNativePolicy.policy_on_menu D (otherProposer j) _
    (by rw [←(NativeRawFactor.offCommon_pair D) hd];exact hm) u]
  have htK : D.E.localTag ((observe (drawsRealization d) (otherProposer j)) i)=0 :=
    (D.E.entry_common_tag (hd i) (Or.inl rfl)).mp hi
  rw [D.policy_low_iff _ _ _ i htK,
    OrderedNativePolicy.lowSelect_label_independent D.E D.ξ D.xi_pos D.xi_lt_one
      (OrderedNativePolicy.role D.E (otherProposer j) _) (otherProposer j) _ u.2]
  change i∈D.E.lowSelect D.ξ D.xi_pos D.xi_lt_one c (otherProposer j) _ u.2 ↔ _
  rw [show D.E.lowContext j L = D.E.lowContext (otherProposer j)
    (observe (drawsRealization d) (otherProposer j)) from D.E.lowContext_pair hd j]
  rfl

include hseed hpolicy hc hr in
theorem raw_mean (hOff : D.offCommon L≠∅) (hf : ∀ f,¬D.UseFocal (OrderedNativePolicy.role D.E j L) f L)
    (i : Fin m) (hi : i∈D.rawCommon L) :
    otherMean Γ κ j L i=D.rawOppositeMean (OrderedNativePolicy.role D.E j L) L
      (rankFin (D.rawCommon L) (bidVector L) ⟨i,hi⟩) := by
  have hj : OrderedNativePolicy.role D.E j L=0 ∨ OrderedNativePolicy.role D.E j L=1 := by
    have hh := (OrderedNativePolicy.role D.E j L).isLt
    omega
  rcases hj with hj | hj
  · rw [hj,(NativeRawFactor.rawOppositeMean_zero D)]
    rw [hj] at hf
    erw [←D.rawMean1_original (D.rawCommon L)
      (D.finiteCount (ids D.E 2 L)) (D.finiteCount (ids D.E 3 L)) L]
    apply sampler_mean Γ κ hseed j L i
      (PairedRawPolicy.one (D.rawCommon L).card (D.finiteCount (ids D.E 2 L)).val (D.finiteCount (ids D.E 3 L)).val
        c D.E.R D.E.Rp D.E.H D.ξ)
      (PairedRawPolicy.measurable_one _ _ _ _ _ _ _ _) _ _
      (measurable_missing_row D j L)
      (D.originalPrivateRow (D.finiteCount (ids D.E 3 L)) : Measure (Row (D.finiteCount (ids D.E 3 L)).val D.E.R D.E.Rp D.E.H)) hr _
    filter_upwards [hc] with d hd
    intro u
    rw [policy_other_compatible D Γ hpolicy j L hd u,hj,(NativeRawFactor.fallback_pair D) hd 0 hOff hf u]
    have hh := (NativeRawFactor.opposite_raw_one D) hd i hi u
    simp only [otherProposer,ite_true,Data.finiteCount] at hh ⊢
    convert! hh using 1
  · rw [hj,(NativeRawFactor.rawOppositeMean_one D)]
    rw [hj] at hf
    erw [←D.rawMean0_original (D.rawCommon L)
      (D.finiteCount (ids D.E 3 L)) (D.finiteCount (ids D.E 2 L)) L]
    apply sampler_mean Γ κ hseed j L i
      (PairedRawPolicy.zero (D.rawCommon L).card (D.finiteCount (ids D.E 3 L)).val (D.finiteCount (ids D.E 2 L)).val
        c D.E.R D.E.Rp D.E.H D.ξ)
      (PairedRawPolicy.measurable_zero _ _ _ _ _ _ _ _) _ _
      (measurable_missing_row D j L)
      (D.originalPrivateRow (D.finiteCount (ids D.E 3 L)) : Measure (Row (D.finiteCount (ids D.E 3 L)).val D.E.R D.E.Rp D.E.H)) hr _
    filter_upwards [hc] with d hd
    intro u
    rw [policy_other_compatible D Γ hpolicy j L hd u,hj,(NativeRawFactor.fallback_pair D) hd 1 hOff hf u]
    have hh := (NativeRawFactor.opposite_raw_zero D) hd i hi u
    simp only [otherProposer,if_neg (by decide : (1:Fin 2)≠0),Data.finiteCount] at hh ⊢
    convert! hh using 1

include hseed hpolicy hc hr in
theorem focal_mean (f : Fin m) (hf : D.UseFocal (OrderedNativePolicy.role D.E j L) f L)
    (x : Option (Fin ((ids D.E 1 L).erase f).card)) :
    otherMean Γ κ j L (commonIdentity f ((ids D.E 1 L).erase f) (bidVector L) x)=
      (NativeFocalFactor.focalOppositeMean D) (OrderedNativePolicy.role D.E j L) f L x := by
  have hj : OrderedNativePolicy.role D.E j L=0 ∨ OrderedNativePolicy.role D.E j L=1 := by
    have hh := (OrderedNativePolicy.role D.E j L).isLt
    omega
  rcases hj with hj | hj
  · rw [hj] at hf ⊢
    simp only [focalOppositeMean,ite_true]
    rw [←(NativeFocalFactor.focalCommonMean1_original D) _ _ _ _ _ ((NativeFocalFactor.FocalUse_zero D) f L hf)]
    apply sampler_mean Γ κ hseed j L _
      (D.oneFocal ((ids D.E 1 L).erase f).card (D.finiteCount (ids D.E 2 L))
        (D.finiteCount (ids D.E 3 L)))
      (D.measurable_oneFocal _ _ _) _ _ (measurable_missing_row D j L)
      (D.originalPrivateRow (D.finiteCount (ids D.E 3 L)) : Measure (Row (D.finiteCount (ids D.E 3 L)).val D.E.R D.E.Rp D.E.H)) hr _
    filter_upwards [hc] with d hd
    have hp : D.UseFocal (otherProposer 0) f (observe (drawsRealization d) (otherProposer j)) :=
      ((NativeRawFactor.UseFocal_pair D) hd 0 f).mp hf
    intro u
    rw [policy_other_compatible D Γ hpolicy j L hd u,hj,D.completed_focal _ _ _ hp u]
    simpa only [otherProposer,ite_true] using (NativeFocalFactor.opposite_focal_one D) hd f hf x u
  · rw [hj] at hf ⊢
    simp only [focalOppositeMean,if_neg (by decide : (1:Fin 2)≠0)]
    rw [←(NativeFocalFactor.focalCommonMean0_original D) _ _ _ _ _ ((NativeFocalFactor.FocalUse_one D) f L hf)]
    apply sampler_mean Γ κ hseed j L _
      (D.zeroFocal ((ids D.E 1 L).erase f).card (D.finiteCount (ids D.E 3 L))
        (D.finiteCount (ids D.E 2 L)))
      (D.measurable_zeroFocal _ _ _) _ _ (measurable_missing_row D j L)
      (D.originalPrivateRow (D.finiteCount (ids D.E 3 L)) : Measure (Row (D.finiteCount (ids D.E 3 L)).val D.E.R D.E.Rp D.E.H)) hr _
    filter_upwards [hc] with d hd
    have hp : D.UseFocal (otherProposer 1) f (observe (drawsRealization d) (otherProposer j)) :=
      ((NativeRawFactor.UseFocal_pair D) hd 1 f).mp hf
    intro u
    rw [policy_other_compatible D Γ hpolicy j L hd u,hj,D.completed_focal _ _ _ hp u]
    simpa only [otherProposer,if_neg (by decide : (1:Fin 2)≠0)] using (NativeFocalFactor.opposite_focal_zero D) hd f hf x u

include hpolicy hc in
theorem focal_low (f : Fin m) (hf : D.UseFocal (OrderedNativePolicy.role D.E j L) f L)
    (i : Fin m) (hi : D.E.localTag (L i)=0) : otherMean Γ κ j L i=0 := by
  apply zero_mean Γ κ j L i
  filter_upwards [hc] with d hd
  have hp := ((NativeRawFactor.UseFocal_pair D) hd (OrderedNativePolicy.role D.E j L) f).mp hf
  have hit := (D.E.entry_common_tag (hd i) (Or.inl rfl)).mp hi
  intro u
  rw [policy_other_compatible D Γ hpolicy j L hd u,D.completed_focal _ _ _ hp u]
  exact (NativeFocalFactor.focal_low_absent D) _ _ _ hp i hit u

end FCAppendix.Affine.Tail04.OrderedNativeCompatibleMeans
