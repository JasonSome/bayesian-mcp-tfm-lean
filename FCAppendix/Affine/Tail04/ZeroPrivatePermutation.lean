import FCAppendix.Affine.Tail04.NativePartialFiberCoordinates

noncomputable section
namespace FCAppendix.Affine.Tail04.ZeroPrivatePermutation
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open NativeLocalPolicy EqualPrivateSignal EqualPrivateUpper LocalHighCommon
open PrivatePartialSorting PrivatePayoffContinuity JoinedHighPolicy

variable {m c : ℕ} (K : NativeLocalPolicy.Data m c) (A : ℕ) (H0 H1 : Fin (m+1))

include H1 in
theorem zero_permutation_regular
    (p : Parameters A H0.val K.E.R K.E.Rp K.E.U)
    (row : Row H0.val K.E.R K.E.Rp K.E.H)
    (j : Fin H0.val) (price : Icc K.E.R K.E.Rp) (hj : row j=Sum.inr price)
    (hreg : H0=H1→ policyInput (c:=c) (ξ:=K.ξ) (equalParameter p) (signal row)∈Regular K.ξ j)
    (hno : ∀ l,l≠j→ numericalEntry (row l)≠(price:ℝ))
    (hgap : (1-K.ξ)*K.E.U< K.E.R)
    (σ τ : Equiv.Perm (Fin H0.val)) (u : unitInterval) :
    (if Sum.inr (σ.symm j)∈K.zeroSampler A H0 H1 (p,reindexRow σ row) u then (1:ℝ) else 0)=
      (if Sum.inr (τ.symm j)∈K.zeroSampler A H0 H1 (p,reindexRow τ row) u then (1:ℝ) else 0) := by
  by_cases he : H0=H1
  · subst H1
    have hσ := equalBase_reindexed_privateValue A H0.val c
      ⟨K.xi_pos.le,K.xi_lt_one.le⟩ (K.E.d_nonneg.trans K.E.d_lt_R.le)
      (K.E.Rp_lt_one.le.trans K.E.one_le_U) K.E.U_lt_H
      (((by norm_num : (0:ℝ)<1).trans_le K.E.one_le_U).trans K.E.U_lt_H)
      (equalParameter p) row σ j price hj (hreg rfl) u
    have hτ := equalBase_reindexed_privateValue A H0.val c
      ⟨K.xi_pos.le,K.xi_lt_one.le⟩ (K.E.d_nonneg.trans K.E.d_lt_R.le)
      (K.E.Rp_lt_one.le.trans K.E.one_le_U) K.E.U_lt_H
      (((by norm_num : (0:ℝ)<1).trans_le K.E.one_le_U).trans K.E.U_lt_H)
      (equalParameter p) row τ j price hj (hreg rfl) u
    simpa only [K.zeroSampler_equal,NativeLocalPolicy.Data.equalSampler,
      AllCountHighPolicy.equalSample] using hσ.trans hτ.symm
  · rw [K.zeroSampler_unequal A H0 H1 he]
    have hσ := joined_reindexed_rank A H0.val H1.val c
      (K.marksLaw H0) (K.marksLaw H1) false K.xi_pos K.xi_lt_one.le K.width_pos
      p row σ (K.E.d_nonneg.trans_lt K.E.d_lt_R)
      (K.E.R_le_Rp.trans K.E.Rp_lt_H.le) K.E.Rp_lt_one hgap K.E.Rp_lt_H
      j price hj hno u
    have hτ := joined_reindexed_rank A H0.val H1.val c
      (K.marksLaw H0) (K.marksLaw H1) false K.xi_pos K.xi_lt_one.le K.width_pos
      p row τ (K.E.d_nonneg.trans_lt K.E.d_lt_R)
      (K.E.R_le_Rp.trans K.E.Rp_lt_H.le) K.E.Rp_lt_one hgap K.E.Rp_lt_H
      j price hj hno u
    exact hσ.trans hτ.symm

theorem one_permutation_regular
    (p : Parameters A H0.val K.E.R K.E.Rp K.E.U)
    (row : Row H1.val K.E.R K.E.Rp K.E.H)
    (j : Fin H1.val) (price : Icc K.E.R K.E.Rp) (hj : row j=Sum.inr price)
    (hreg : ∀ he : H1.val=H0.val,
      policyInput (c:=c) (ξ:=K.ξ) (equalParameter p)
        (fun l=> signal row (Fin.cast he.symm l))∈Regular K.ξ (Fin.cast he j))
    (hno : ∀ l,l≠j→ numericalEntry (row l)≠(price:ℝ))
    (hgap : (1-K.ξ)*K.E.U< K.E.R)
    (σ τ : Equiv.Perm (Fin H1.val)) (u : unitInterval) :
    (if Sum.inr (σ.symm j)∈K.oneSampler A H0 H1 (p,reindexRow σ row) u then (1:ℝ) else 0)=
      (if Sum.inr (τ.symm j)∈K.oneSampler A H0 H1 (p,reindexRow τ row) u then (1:ℝ) else 0) := by
  by_cases he : H0=H1
  · subst H1
    rw [K.oneSampler_equal]
    have hr : H0=H0→policyInput (c:=c) (ξ:=K.ξ) (equalParameter p)
        (signal row)∈Regular K.ξ j := by
      intro _
      simpa only [Fin.cast_refl] using! hreg rfl
    simpa only [K.zeroSampler_equal] using!
      zero_permutation_regular K A H0 H0 p row j price hj hr hno hgap σ τ u
  · rw [K.oneSampler_unequal A H0 H1 he]
    have hσ := joined_reindexed_rank A H0.val H1.val c
      (K.marksLaw H0) (K.marksLaw H1) true K.xi_pos K.xi_lt_one.le K.width_pos
      p row σ (K.E.d_nonneg.trans_lt K.E.d_lt_R)
      (K.E.R_le_Rp.trans K.E.Rp_lt_H.le) K.E.Rp_lt_one hgap K.E.Rp_lt_H
      j price hj hno u
    have hτ := joined_reindexed_rank A H0.val H1.val c
      (K.marksLaw H0) (K.marksLaw H1) true K.xi_pos K.xi_lt_one.le K.width_pos
      p row τ (K.E.d_nonneg.trans_lt K.E.d_lt_R)
      (K.E.R_le_Rp.trans K.E.Rp_lt_H.le) K.E.Rp_lt_one hgap K.E.Rp_lt_H
      j price hj hno u
    exact hσ.trans hτ.symm

end FCAppendix.Affine.Tail04.ZeroPrivatePermutation
