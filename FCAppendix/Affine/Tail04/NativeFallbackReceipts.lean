import FCAppendix.Affine.Tail04.NativeCompatibleMeans
import FCAppendix.Affine.Tail04.PrivateFallbackKernel

noncomputable section
namespace FCAppendix.Affine.Tail04.NativeFallbackReceipts
open MeasureTheory ProbabilityTheory Set Classical Filter Game Bayes
open LocalCoordinates SortedCoordinates NativeLocalPolicy NativeObservationPair NativePolicyFactor
open NativeRawFactor NativeFocalFactor NativeFocalVector NativeKernelIntegration NativeCompatibleMeans
open JoinedHighPolicy EqualPrivateSignal EqualPrivateUpper Hybrid PosteriorReceiptNormalization

variable {m c : ℕ} (D : Data m c)
    (ρ : ProbabilityMeasure (PrivateFallbackKernel.Entry D.E))
    (hrows : ∀ H : Fin (m+1),D.originalPrivateRow H=
      PrivateRowSorting.sortedOriginalIid D.E H.val ρ)
    (Γ : FiniteGame m 2 c Seed) (hseed : Γ.seedLaw=seedLaw)
    (hpolicy : ∀ j,Γ.policy j=D.completedPolicy j)
local notation "κ" => PrivateFallbackKernel.kernel D.E ρ

lemma kernel_compatible (j : Fin 2) (L : LocalList m) (hL : NonnegativeList L) :
    ∀ᵐ d ∂κ j L,D.E.Compatible L (observe (drawsRealization d) (otherProposer j)) := by
  change ∀ᵐ d ∂(PrivateFallbackKernel.latentLaw D.E ρ).map (PrivateFallbackKernel.profile D.E j L),_
  apply (ae_map_iff ((PrivateFallbackKernel.measurable_profile D.E j).comp measurable_prodMk_left).aemeasurable
    ((D.E.measurableSet_compatible L).preimage (measurable_observe_draws (otherProposer j)))).mpr
  apply ae_of_all
  intro x
  change D.E.Compatible L (observe (drawsRealization (PrivateFallbackKernel.profile D.E j L x)) (otherProposer j))
  rw [PrivateFallbackKernel.observe_other D.E j L hL x]
  exact PrivateFallbackKernel.compatible_otherList D.E L x

include hrows in
lemma kernel_original_row (j : Fin 2) (L : LocalList m) (hL : NonnegativeList L) :
    (κ j L).map (fun d => privateRow D.E (ids D.E 3 L)
      (observe (drawsRealization d) (otherProposer j)))=
      (D.originalPrivateRow (D.finiteCount (ids D.E 3 L)) : Measure (Row (D.finiteCount (ids D.E 3 L)).val D.E.R D.E.Rp D.E.H)) := by
  rw [hrows]
  exact PrivateFallbackKernel.kernel_privateRow_law D.E ρ j L hL

variable (η : ℝ) (hη0 : 0≤ η) (hη1 : η≤1)
    (hA : Γ.A=Schedule.affine 2 η hη0 hη1) (hcoef : (1-η)/2=D.ξ)

include hrows hseed hpolicy η hη0 hη1 hA hcoef in
theorem receipts_eq (j : Fin 2) (L : LocalList m) (hL : NonnegativeList L) :
    receipts Γ κ j L=D.completedNumericalReceipt j L := by
  have hc := kernel_compatible D ρ j L hL
  have hr := kernel_original_row D ρ hrows j L hL
  have hprivate (i : Fin m) (hi : D.E.localTag (L i)=2) : otherMean Γ κ j L i=0 :=
    NativeCompatibleMeans.private_mean D Γ κ hpolicy j L hc i hi
  have ha (i : Fin m) : receipts Γ κ j L i=
      entryBid (L i)*(1-D.ξ*otherMean Γ κ j L i) := by
    rw [affine_receipts Γ κ η hη0 hη1 hA j L i,hcoef]
  cases he : D.offCandidate L with
  | none =>
    have hm : D.offCommon L=∅ := (Data.firstOff_none _).mp he
    rw [D.completedNumericalReceipt_on_menu j L hm]
    funext i
    rw [ha]
    cases hentry : L i with
    | none => simp [entryBid,D.numericalReceipt_absent j L i hentry]
    | some b =>
      generalize hi : D.E.localTag (L i)=k
      fin_cases k
      · rw [NativeCompatibleMeans.onMenu_low D Γ κ hseed hpolicy j L hc hm i hi]
        simpa only [hentry] using (D.numericalReceipt_low_formula j L i hi).symm
      · have hiA : i∈ids D.E 1 L := by simp [ids,hi]
        rw [NativeCompatibleMeans.onMenu_active D Γ κ hseed hpolicy j L hc hr hm i hiA]
        simpa only [hentry] using (D.numericalReceipt_active j L i hiA ((D.offCommon_eq_empty_iff L).mp hm i hi)).symm
      · rw [hprivate i hi]
        have hiP : i∈ids D.E 2 L := by simp [ids,hi]
        simpa only [mul_zero,sub_zero,mul_one,hentry] using (D.numericalReceipt_private j L i hiP).symm
      · have hn := (D.E.localTag_absent (L i)).mp hi
        simp [hentry] at hn
  | some f =>
    by_cases hf : D.UseFocal j f L
    · simp only [Data.completedNumericalReceipt,he,if_pos hf]
      funext i
      rw [ha,(NativeFocalVector.focalNumericalReceipt_all D) j f L hf i]
      by_cases hn : L i=none
      · simp [hn,entryBid]
      · suffices heq : otherMean Γ κ j L i=(NativeFocalVector.focalOppositeIdentityMean D) j f L i by rw [heq]
        generalize hit : D.E.localTag (L i)=k
        fin_cases k
        · rw [NativeCompatibleMeans.focal_low D Γ κ hpolicy j L hc f hf i hit,
            (NativeFocalVector.focalOppositeIdentityMean_low D) j f L hf i hit]
        · by_cases hif : i=f
          · subst i
            have hh := NativeCompatibleMeans.focal_mean D Γ κ hseed hpolicy j L hc hr f hf none
            simpa [commonIdentity,focalOppositeIdentityMean] using hh
          · have hiA : i∈(ids D.E 1 L).erase f := by simp [ids,hit,hif]
            have hh := NativeCompatibleMeans.focal_mean D Γ κ hseed hpolicy j L hc hr f hf
              (some (rankFin ((ids D.E 1 L).erase f) (bidVector L) ⟨i,hiA⟩))
            simpa [commonIdentity,focalOppositeIdentityMean,hif,hiA,enumerate_rank] using hh
        · rw [hprivate i hit,(NativeFocalVector.focalOppositeIdentityMean_private D) j f L hf i hit]
        · exact (hn ((D.E.localTag_absent (L i)).mp hit)).elim
    · have hOff : D.offCommon L≠∅ := by
        intro hh
        have hn : D.offCandidate L=none := (Data.firstOff_none _).mpr hh
        simp [he] at hn
      have hnone : ∀ g,¬D.UseFocal j g L := by
        intro g hg
        have hcand : D.offCandidate L=some g := by
          simp [Data.offCandidate,hg.1,Data.firstOff_singleton]
        have hfg : f=g := Option.some.inj (he.symm.trans hcand)
        subst g
        exact hf hg
      simp only [Data.completedNumericalReceipt,he,if_neg hf]
      funext i
      rw [ha]
      cases hentry : L i with
      | none => simp [entryBid,D.rawNumericalReceipt_absent j L i hentry]
      | some b =>
        generalize hit : D.E.localTag (L i)=k
        fin_cases k
        · have hiC : i∈D.rawCommon L := by simp [Data.rawCommon,ids,hit]
          rw [NativeCompatibleMeans.raw_mean D Γ κ hseed hpolicy j L hc hr hOff hnone i hiC]
          simpa only [hentry] using (D.rawNumericalReceipt_common j L i hiC).symm
        · have hiC : i∈D.rawCommon L := by simp [Data.rawCommon,ids,hit]
          rw [NativeCompatibleMeans.raw_mean D Γ κ hseed hpolicy j L hc hr hOff hnone i hiC]
          simpa only [hentry] using (D.rawNumericalReceipt_common j L i hiC).symm
        · rw [hprivate i hit]
          have hiP : i∈ids D.E 2 L := by simp [ids,hit]
          simpa only [mul_zero,sub_zero,mul_one,hentry] using (D.rawNumericalReceipt_private j L i hiP).symm
        · have hn := (D.E.localTag_absent (L i)).mp hit
          simp [hentry] at hn

include hrows hseed hpolicy η hη0 hη1 hA hcoef in
theorem optimal (hlow : D.E.d<1-D.ξ) (j : Fin 2) (L : LocalList m)
    (hL : NonnegativeList L) (u : Seed) :
    Finite.Optimal c (receipts Γ κ j L) ((Γ.policy j L u).val) := by
  rw [receipts_eq D ρ hrows Γ hseed hpolicy η hη0 hη1 hA hcoef j L hL,hpolicy j]
  exact D.completed_numerical_optimal hlow j L hL u

end FCAppendix.Affine.Tail04.NativeFallbackReceipts
