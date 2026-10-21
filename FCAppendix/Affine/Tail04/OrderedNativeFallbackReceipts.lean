import FCAppendix.Affine.Tail04.NativeFallbackReceipts
import FCAppendix.Affine.Tail04.OrderedNativeCompatibleMeans
import FCAppendix.Affine.Tail04.OrderedNativeBayesianReceipts
import FCAppendix.Affine.Tail04.PrivateFallbackKernel

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedNativeFallbackReceipts
open MeasureTheory ProbabilityTheory Set Classical Filter Game Bayes
open LocalCoordinates SortedCoordinates NativeLocalPolicy NativeObservationPair NativePolicyFactor
open NativeRawFactor NativeFocalFactor NativeFocalVector NativeKernelIntegration
open JoinedHighPolicy EqualPrivateSignal EqualPrivateUpper Hybrid PosteriorReceiptNormalization

variable {m c : ℕ} (D : Data m c)
    (ρ : ProbabilityMeasure (PrivateFallbackKernel.Entry D.E))
    (hrows : ∀ H : Fin (m+1),D.originalPrivateRow H=
      PrivateRowSorting.sortedOriginalIid D.E H.val ρ)
    (Γ : FiniteGame m 2 c Seed) (hseed : Γ.seedLaw=seedLaw)
    (hpolicy : ∀ j,Γ.policy j=OrderedNativePolicy.policy D j)
local notation "κ" => PrivateFallbackKernel.kernel D.E ρ

variable (η : ℝ) (hη0 : 0≤ η) (hη1 : η≤1)
    (hA : Γ.A=Schedule.affine 2 η hη0 hη1) (hcoef : (1-η)/2=D.ξ)

include hrows hseed hpolicy η hη0 hη1 hA hcoef in
theorem receipts_eq (j : Fin 2) (L : LocalList m) (hL : NonnegativeList L) :
    receipts Γ κ j L=D.completedNumericalReceipt (OrderedNativePolicy.role D.E j L) L := by
  have hc := NativeFallbackReceipts.kernel_compatible D ρ j L hL
  have hr := NativeFallbackReceipts.kernel_original_row D ρ hrows j L hL
  have hprivate (i : Fin m) (hi : D.E.localTag (L i)=2) : otherMean Γ κ j L i=0 :=
    OrderedNativeCompatibleMeans.private_mean D Γ κ hpolicy j L hc i hi
  have ha (i : Fin m) : receipts Γ κ j L i=
      entryBid (L i)*(1-D.ξ*otherMean Γ κ j L i) := by
    rw [affine_receipts Γ κ η hη0 hη1 hA j L i,hcoef]
  cases he : D.offCandidate L with
  | none =>
    have hm : D.offCommon L=∅ := (Data.firstOff_none _).mp he
    rw [D.completedNumericalReceipt_on_menu (OrderedNativePolicy.role D.E j L) L hm]
    funext i
    rw [ha]
    cases hentry : L i with
    | none => simp [entryBid,D.numericalReceipt_absent (OrderedNativePolicy.role D.E j L) L i hentry]
    | some b =>
      generalize hi : D.E.localTag (L i)=k
      fin_cases k
      · rw [OrderedNativeCompatibleMeans.onMenu_low D Γ κ hseed hpolicy j L hc hm i hi,
          OrderedNativeBayesianReceipts.opposite_low_acceptance_label_independent D j
            (OrderedNativePolicy.role D.E j L) L i]
        simpa only [hentry] using (D.numericalReceipt_low_formula (OrderedNativePolicy.role D.E j L) L i hi).symm
      · have hiA : i∈ids D.E 1 L := by simp [ids,hi]
        rw [OrderedNativeCompatibleMeans.onMenu_active D Γ κ hseed hpolicy j L hc hr hm i hiA]
        simpa only [hentry] using (D.numericalReceipt_active (OrderedNativePolicy.role D.E j L) L i hiA ((D.offCommon_eq_empty_iff L).mp hm i hi)).symm
      · rw [hprivate i hi]
        have hiP : i∈ids D.E 2 L := by simp [ids,hi]
        simpa only [mul_zero,sub_zero,mul_one,hentry] using (D.numericalReceipt_private (OrderedNativePolicy.role D.E j L) L i hiP).symm
      · have hn := (D.E.localTag_absent (L i)).mp hi
        simp [hentry] at hn
  | some f =>
    by_cases hf : D.UseFocal (OrderedNativePolicy.role D.E j L) f L
    · simp only [Data.completedNumericalReceipt,he,if_pos hf]
      funext i
      rw [ha,(NativeFocalVector.focalNumericalReceipt_all D) (OrderedNativePolicy.role D.E j L) f L hf i]
      by_cases hn : L i=none
      · simp [hn,entryBid]
      · suffices heq : otherMean Γ κ j L i=(NativeFocalVector.focalOppositeIdentityMean D) (OrderedNativePolicy.role D.E j L) f L i by rw [heq]
        generalize hit : D.E.localTag (L i)=k
        fin_cases k
        · rw [OrderedNativeCompatibleMeans.focal_low D Γ κ hpolicy j L hc f hf i hit,
            (NativeFocalVector.focalOppositeIdentityMean_low D) (OrderedNativePolicy.role D.E j L) f L hf i hit]
        · by_cases hif : i=f
          · subst i
            have hh := OrderedNativeCompatibleMeans.focal_mean D Γ κ hseed hpolicy j L hc hr f hf none
            simpa [commonIdentity,focalOppositeIdentityMean] using hh
          · have hiA : i∈(ids D.E 1 L).erase f := by simp [ids,hit,hif]
            have hh := OrderedNativeCompatibleMeans.focal_mean D Γ κ hseed hpolicy j L hc hr f hf
              (some (rankFin ((ids D.E 1 L).erase f) (bidVector L) ⟨i,hiA⟩))
            simpa [commonIdentity,focalOppositeIdentityMean,hif,hiA,enumerate_rank] using hh
        · rw [hprivate i hit,(NativeFocalVector.focalOppositeIdentityMean_private D) (OrderedNativePolicy.role D.E j L) f L hf i hit]
        · exact (hn ((D.E.localTag_absent (L i)).mp hit)).elim
    · have hOff : D.offCommon L≠∅ := by
        intro hh
        have hn : D.offCandidate L=none := (Data.firstOff_none _).mpr hh
        simp [he] at hn
      have hnone : ∀ g,¬D.UseFocal (OrderedNativePolicy.role D.E j L) g L := by
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
      | none => simp [entryBid,D.rawNumericalReceipt_absent (OrderedNativePolicy.role D.E j L) L i hentry]
      | some b =>
        generalize hit : D.E.localTag (L i)=k
        fin_cases k
        · have hiC : i∈D.rawCommon L := by simp [Data.rawCommon,ids,hit]
          rw [OrderedNativeCompatibleMeans.raw_mean D Γ κ hseed hpolicy j L hc hr hOff hnone i hiC]
          simpa only [hentry] using (D.rawNumericalReceipt_common (OrderedNativePolicy.role D.E j L) L i hiC).symm
        · have hiC : i∈D.rawCommon L := by simp [Data.rawCommon,ids,hit]
          rw [OrderedNativeCompatibleMeans.raw_mean D Γ κ hseed hpolicy j L hc hr hOff hnone i hiC]
          simpa only [hentry] using (D.rawNumericalReceipt_common (OrderedNativePolicy.role D.E j L) L i hiC).symm
        · rw [hprivate i hit]
          have hiP : i∈ids D.E 2 L := by simp [ids,hit]
          simpa only [mul_zero,sub_zero,mul_one,hentry] using (D.rawNumericalReceipt_private (OrderedNativePolicy.role D.E j L) L i hiP).symm
        · have hn := (D.E.localTag_absent (L i)).mp hit
          simp [hentry] at hn

include hrows hseed hpolicy η hη0 hη1 hA hcoef in
theorem optimal (hlow : D.E.d<1-D.ξ) (j : Fin 2) (L : LocalList m)
    (hL : NonnegativeList L) (u : Seed) :
    Finite.Optimal c (receipts Γ κ j L) ((Γ.policy j L u).val) := by
  rw [receipts_eq D ρ hrows Γ hseed hpolicy η hη0 hη1 hA hcoef j L hL,hpolicy j]
  exact OrderedNativePolicy.numerical_optimal D hlow j L hL u

end FCAppendix.Affine.Tail04.OrderedNativeFallbackReceipts
