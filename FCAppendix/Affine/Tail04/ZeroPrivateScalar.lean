import FCAppendix.Affine.Tail04.ZeroPrivateRegularity
import FCAppendix.Affine.Tail04.NativePartialProductReduction

noncomputable section
namespace FCAppendix.Affine.Tail04.ZeroPrivateScalar
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open NativeLocalPolicy NativePartialExperiment NativePartialProductReduction
open EqualPrivateSignal EqualPrivateUpper PrivateRowSorting PrivatePartialSorting
open PrivatePayoffContinuity LocalHighCommon JoinedPartialNoisy

theorem rank_signal_update (A H0 H1 c : ℕ) {R U H : ℝ} (side : Bool)
    (j : Fin (AllCountAtypical.ownCount H0 H1 side))
    (row : Row (AllCountAtypical.ownCount H0 H1 side) R U H) (price : Icc R U) :
    AtypicalPartialNoisy.rankInclusion A H0 H1 c side j
      ((price:ℝ),signal (Function.update row j (Sum.inr price)))=
    AtypicalPartialNoisy.rankInclusion A H0 H1 c side j ((price:ℝ),signal row) := by
  unfold AtypicalPartialNoisy.rankInclusion
  congr 2
  congr 1
  ext l
  by_cases hl : l=j
  · subst l;simp [AtypicalPartialNoisy.rivalsAbove]
  · simp [AtypicalPartialNoisy.rivalsAbove,signal,Function.update_of_ne hl]

theorem signal_update {K : ℕ} {R U H : ℝ} (row : Row K R U H)
    (j : Fin K) (price : Icc R U) :
    signal (Function.update row j (Sum.inr price))=
      Function.update (signal row) j (Sum.inr price) := by
  funext l
  by_cases hl : l=j
  · subst l;simp only [signal,Function.update_self,signalEntry]
  · simp only [signal,Function.update_of_ne hl]

variable {m c : ℕ} (K : NativeLocalPolicy.Data m c) (A : ℕ)

theorem measurable_value (H0 H1 : Fin (m+1)) (Q : PublicScenario.Data) (side low : Bool)
    (j : Fin (ownH H0 H1 side).val) (v : ℝ) :
    Measurable (fun x : Icc K.E.R K.E.Rp×((Fin A→ Icc (1:ℝ) K.E.U)×
      (Row (ownH H0 H1 side).val K.E.R K.E.Rp K.E.H×(unitInterval×unitInterval)))=>
      value K A H0 H1 Q side low j v x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2) :=
  (measurable_const.sub measurable_fst.subtype_val).mul
    ((measurable_inclusion K A H0 H1 Q side low j).comp measurable_snd)

include A in
theorem equal_value_zero (H : Fin (m+1)) (Q : PublicScenario.Data) (low : Bool)
    (j : Fin H.val) (price : Icc K.E.R K.E.Rp) (v : ℝ)
    (common : Fin A→ Icc (1:ℝ) K.E.U) (row : Row H.val K.E.R K.E.Rp K.E.H)
    (hj : row j=Sum.inr price)
    (hreg : policyInput (c:=c) (ξ:=K.ξ) (SortedAllNoise.sortedBox common,K.signalLaw H)
      (signal row)∈Regular K.ξ j) (pub u : unitInterval) :
    value K A H H Q false low j v price common row pub u=
      (v-price)*privateValue (c:=c) K.ξ j
        (policyInput (c:=c) (ξ:=K.ξ) (SortedAllNoise.sortedBox common,K.signalLaw H) (signal row)) := by
  have hs := equalBase_reindexed_privateValue A H.val c
    ⟨K.xi_pos.le,K.xi_lt_one.le⟩ (K.E.d_nonneg.trans K.E.d_lt_R.le)
    (K.E.Rp_lt_one.le.trans K.E.one_le_U) K.E.U_lt_H
    (((by norm_num : (0:ℝ)<1).trans_le K.E.one_le_U).trans K.E.U_lt_H)
    (SortedAllNoise.sortedBox common,K.signalLaw H) row (Equiv.refl _) j price hj hreg u
  simpa only [value,NativePartialExperiment.inclusion,sampler_false,K.zeroSampler_equal,
    NativeLocalPolicy.Data.equalSampler,AllCountHighPolicy.equalSample,
    publicParameter,JoinedHighPolicy.equalParameter,JoinedPartialPublicIntegral.parameters,
    PrivatePartialSorting.reindexRow,Equiv.refl_symm,Equiv.refl_apply] using! congrArg (fun x=>(v-price)*x) hs

include A in
theorem equal_value_one (H : Fin (m+1)) (Q : PublicScenario.Data) (low : Bool)
    (j : Fin H.val) (price : Icc K.E.R K.E.Rp) (v : ℝ)
    (common : Fin A→ Icc (1:ℝ) K.E.U) (row : Row H.val K.E.R K.E.Rp K.E.H)
    (hj : row j=Sum.inr price)
    (hreg : policyInput (c:=c) (ξ:=K.ξ) (SortedAllNoise.sortedBox common,K.signalLaw H)
      (signal row)∈Regular K.ξ j) (pub u : unitInterval) :
    value K A H H Q true low j v price common row pub u=
      (v-price)*privateValue (c:=c) K.ξ j
        (policyInput (c:=c) (ξ:=K.ξ) (SortedAllNoise.sortedBox common,K.signalLaw H) (signal row)) := by
  simpa only [value,NativePartialExperiment.inclusion,sampler_true,K.oneSampler_equal,sampler_false,K.zeroSampler_equal]
    using! equal_value_zero K A H Q low j price v common row hj hreg pub u

theorem unequal_inclusion (H0 H1 : Fin (m+1)) (h : H0≠H1)
    (Q : PublicScenario.Data) (side low : Bool)
    (j : Fin (ownH H0 H1 side).val) (price : Icc K.E.R K.E.Rp)
    (common : Fin A→ Icc (1:ℝ) K.E.U)
    (row : Row (ownH H0 H1 side).val K.E.R K.E.Rp K.E.H)
    (hj : row j=Sum.inr price)
    (hno : ∀ l,l≠j→ numericalEntry (row l)≠(price:ℝ))
    (hgap : (1-K.ξ)*K.E.U< K.E.R) (pub u : unitInterval) :
    NativePartialExperiment.inclusion K A H0 H1 Q side low j common row pub u=
      if JoinedHighPolicy.UseTypical A H0.val H1.val c K.ξ K.E.U K.E.R K.E.Rp K.width
        (K.marksLaw H0) (K.marksLaw H1)
        (publicParameter K A H0 H1 Q low common pub) then
          (if JoinedHighPolicy.regime (publicParameter K A H0 H1 Q low common pub).1.1 then 0 else 1)
      else AtypicalPartialNoisy.rankInclusion A H0.val H1.val c side j ((price:ℝ),signal row) := by
  have hs := joined_reindexed_rank A H0.val H1.val c (K.marksLaw H0) (K.marksLaw H1)
    side K.xi_pos K.xi_lt_one.le K.width_pos (publicParameter K A H0 H1 Q low common pub)
    row (Equiv.refl _) (K.E.d_nonneg.trans_lt K.E.d_lt_R)
    (K.E.R_le_Rp.trans K.E.Rp_lt_H.le) K.E.Rp_lt_one hgap K.E.Rp_lt_H j price hj hno u
  have hsam : sampler K A H0 H1 side=
      unequalSide A H0.val H1.val c K.ξ K.E.U K.E.R K.E.Rp K.E.H K.width
        (K.marksLaw H0) (K.marksLaw H1) side := by
    cases side
    · exact K.zeroSampler_unequal A H0 H1 h
    · exact K.oneSampler_unequal A H0 H1 h
  simpa only [NativePartialExperiment.inclusion,hsam,PrivatePartialSorting.reindexRow,Equiv.refl_symm,Equiv.refl_apply] using! hs

end FCAppendix.Affine.Tail04.ZeroPrivateScalar
