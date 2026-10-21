import FCAppendix.Affine.Hybrid.ActiveNoisyRow

noncomputable section
namespace FCAppendix.Affine.Hybrid
open Set Filter Topology Classical
open scoped BigOperators
variable {N : ℕ}

lemma activePatternIndex_card (kind : Fin N→Fin 4) :
    Fintype.card (ActivePatternIndex kind)=1+categoryCount 1 kind := by
  rw [Fintype.card_subtype,Finset.card_eq_sum_ones,Finset.sum_filter,Fin.sum_univ_succ]
  simp only [activePatternPred,Fin.cases_zero,Fin.cases_succ,if_true,categoryCount,LowBody.hitCount]
  rfl

namespace GuardedData
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def swapOwners (Q : GuardedData ι) : GuardedData ι where
  xi:=Q.xi
  xi_pos:=Q.xi_pos
  xi_lt_one:=Q.xi_lt_one
  bid:=Q.bid
  bid_pos:=Q.bid_pos
  owner₁:=Q.owner₂
  owner₂:=Q.owner₁
  owners_disjoint:=Q.owners_disjoint.symm
  residual:=Q.residual
  mixed_nonempty:=by simpa only [Finset.union_comm] using Q.mixed_nonempty
  lower_guard:=by simpa only [Finset.union_comm] using Q.lower_guard
  upper_guard:=by simpa only [Finset.union_comm] using Q.upper_guard

end GuardedData

theorem activePattern_guardedData {xi L U : ℝ} (hxi : 0<xi) (hxi1 : xi<1) (hL : 0<L)
    (c : ℕ) (z : ℝ) (kind : Fin N→Fin 4) (hg : activePatternGuarded xi L U c z kind)
    (b : ActivePatternIndex kind→ℝ) (hb : ∀i,b i∈Icc L U)
    (E0 E1 : Finset (ActivePatternIndex kind))
    (hE : (sourceOwnersLaw b (activePatternOwner c z kind 0)
      (activePatternOwner c z kind 1)).mass (E0,E1)≠0) :
    ∃Q : GuardedData (ActivePatternIndex kind),Q.xi=xi ∧ Q.bid=b ∧ Q.owner₁=E0 ∧ Q.owner₂=E1 ∧
      Q.residual=activePatternResidual c z kind ∧
      Q.owner₁.card+Q.residual=activePatternCapacity c kind 0 ∧
      Q.owner₂.card+Q.residual=activePatternCapacity c kind 1 := by
  obtain ⟨hE0,hE1,hdis⟩:=sourceOwnersLaw_support b _ _ hg.1 hg.2.2.2.1.le E0 E1 hE
  rcases lt_or_gt_of_ne hg.2.1 with hd | hd
  · have hown0 : activePatternOwner c z kind 0=activePatternQuota z kind := by
      simp [activePatternOwner,not_lt_of_ge hd.le]
    have hown1 : activePatternOwner c z kind 1=activePatternQuota z kind+
        (activePatternCapacity c kind 1-activePatternCapacity c kind 0) := by
      simp [activePatternOwner,hd,activePatternGap,residualDifference,min_eq_left hd.le,max_eq_right hd.le]
    have hrgn := hg.2.2.2.2.1
    simp only [activePatternSmall,activePatternGap,residualDifference,
      min_eq_left hd.le,max_eq_right hd.le] at hrgn
    obtain ⟨Q,hqx,hqb,hq1,hq2,hqr,hql,hqs⟩:=exists_guardedData_of_count_region hxi hxi1 hL
      (N+1) (Fintype.card (ActivePatternIndex kind)) (activePatternCapacity c kind 0)
      (activePatternCapacity c kind 1) (activePatternQuota z kind) (by omega) rfl hd.le hrgn b hb
      E1 E0 hdis.symm (by simpa only [hown1] using hE1) (by simpa only [hown0] using hE0)
    refine ⟨Q.swapOwners,hqx,hqb,hq2,hq1,?_,hqs,hql⟩
    simpa only [GuardedData.swapOwners,activePatternResidual,activePatternSmall,min_eq_left hd.le] using hqr
  · have hown0 : activePatternOwner c z kind 0=activePatternQuota z kind+
        (activePatternCapacity c kind 0-activePatternCapacity c kind 1) := by
      simp [activePatternOwner,hd,activePatternGap,residualDifference,min_eq_right hd.le,max_eq_left hd.le]
    have hown1 : activePatternOwner c z kind 1=activePatternQuota z kind := by
      simp [activePatternOwner,not_lt_of_ge hd.le]
    have hrgn := hg.2.2.2.2.1
    simp only [activePatternSmall,activePatternGap,residualDifference,
      min_eq_right hd.le,max_eq_left hd.le] at hrgn
    obtain ⟨Q,hqx,hqb,hq1,hq2,hqr,hql,hqs⟩:=exists_guardedData_of_count_region hxi hxi1 hL
      (N+1) (Fintype.card (ActivePatternIndex kind)) (activePatternCapacity c kind 1)
      (activePatternCapacity c kind 0) (activePatternQuota z kind) (by omega) rfl hd.le hrgn b hb
      E0 E1 hdis (by simpa only [hown0] using hE0) (by simpa only [hown1] using hE1)
    refine ⟨Q,hqx,hqb,hq1,hq2,?_,hql,hqs⟩
    simpa only [activePatternResidual,activePatternSmall,min_eq_right hd.le] using hqr

end FCAppendix.Affine.Hybrid
