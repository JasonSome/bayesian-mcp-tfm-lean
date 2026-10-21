import FCAppendix.Affine.EqualCapacityPolicy

noncomputable section
namespace FCAppendix.Affine.EqualCapacity
open Set MeasureTheory Game Classical
open Existence.PayOnceBounded (positiveSupport mem_positiveSupport listBids)
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem kernel_underloaded {ξ : ℝ} (hξ : 0<ξ) (hξ1 : ξ<1) (c : ℕ)
    (b : ι→ℝ) (hb : ∀i,0<b i) (hc : Fintype.card ι≤c) :
    kernelMarginal ξ c b=fun _=>1 := by
  have hone : IsKernel ξ c b (fun _=>1) := by
    refine ⟨fun _=>zero_le_one,fun _=>le_rfl,?_,0,le_rfl,?_,?_,?_⟩
    · simp [Nat.min_eq_right hc]
    · intro i hi; norm_num at hi
    · intro i _
      change 0≤b i*(1-ξ*1)
      exact mul_nonneg (hb i).le (by linarith)
    · intro i _ hi; norm_num at hi
  exact isKernel_unique hξ c b hb _ _ (kernelMarginal_spec hξ hξ1 c b hb) hone

theorem positiveMarginal_threshold {ξ : ℝ} (hξ : 0<ξ) (hξ1 : ξ<1)
    (c : ℕ) (b : ι→ℝ) :
    ∃z,0≤z ∧ Proposer.Threshold (positiveMarginal ξ c b)
      (fun i=>b i*(1-ξ*positiveMarginal ξ c b i)) z ∧
      z*((c:ℝ)-(∑i,positiveMarginal ξ c b i))=0 := by
  let S := positiveSupport b
  have hb (i : S) : 0<b i.1 := (mem_positiveSupport b i.1).mp i.2
  by_cases hc : S.card≤c
  · have hk : kernelMarginal ξ c (fun i : S=>b i.1)=fun _=>1 :=
      kernel_underloaded hξ hξ1 c _ hb (by simpa using hc)
    have hp (i : ι) : positiveMarginal ξ c b i=if 0<b i then 1 else 0 := by
      change onSupport ξ c S b i= _
      by_cases hi : i∈S
      · have hbi := (mem_positiveSupport b i).mp hi
        rw [onSupport,dif_pos hi,hk,if_pos hbi]
      · have hbi : ¬0<b i := fun h=>hi ((mem_positiveSupport b i).mpr h)
        rw [onSupport,dif_neg hi,if_neg hbi]
    refine ⟨0,le_rfl,?_,by simp⟩
    refine ⟨?_,?_,?_⟩
    · intro i hi
      have hbi : b i≤0 := by
        by_contra hn
        rw [hp i,if_pos (lt_of_not_ge hn)] at hi
        norm_num at hi
      simpa only [hi,mul_zero,sub_zero,mul_one] using hbi
    · intro i hi
      have hbi : 0≤b i := by
        by_contra hn
        rw [hp i,if_neg (not_lt_of_ge (le_of_lt (lt_of_not_ge hn)))] at hi
        norm_num at hi
      change 0≤b i*(1-ξ*positiveMarginal ξ c b i)
      rw [hi]
      exact mul_nonneg hbi (by linarith)
    · intro i hi hlo
      rw [hp i] at hi hlo
      by_cases hbi : 0<b i <;> simp [hbi] at hi hlo
  · obtain ⟨_,_,hs,z,hz,ht⟩ := kernelMarginal_spec hξ hξ1 c (fun i : S=>b i.1) hb
    have hsum := (positiveMarginal_spec ξ c hξ hξ1 b).2.2
    have he : min c (positiveSupport b).card=c := Nat.min_eq_left (le_of_lt (lt_of_not_ge hc))
    rw [he] at hsum
    refine ⟨z,hz,?_,by rw [hsum]; simp⟩
    refine ⟨?_,?_,?_⟩
    · intro i hi
      by_cases hiS : i∈S
      · dsimp only [S] at hiS
        simpa only [positiveMarginal,onSupport,dif_pos hiS] using
          ht.1 ⟨i,hiS⟩ (by simpa only [positiveMarginal,onSupport,dif_pos hiS] using hi)
      · have hbi : b i≤0 := le_of_not_gt (fun h=>hiS ((mem_positiveSupport b i).mpr h))
        simpa only [hi,mul_zero,sub_zero,mul_one] using hbi.trans hz
    · intro i hi
      have hiS : i∈S := by
        by_contra hn
        rw [positiveMarginal,onSupport,dif_neg hn] at hi
        norm_num at hi
      dsimp only [S] at hiS
      simpa only [positiveMarginal,onSupport,dif_pos hiS] using
        ht.2.1 ⟨i,hiS⟩ (by simpa only [positiveMarginal,onSupport,dif_pos hiS] using hi)
    · intro i hi hlo
      have hiS : i∈S := by
        by_contra hn
        rw [positiveMarginal,onSupport,dif_neg hn] at hi
        norm_num at hi
      dsimp only [S] at hiS
      simpa only [positiveMarginal,onSupport,dif_pos hiS] using
        ht.2.2 ⟨i,hiS⟩ (by simpa only [positiveMarginal,onSupport,dif_pos hiS] using hi)
          (by simpa only [positiveMarginal,onSupport,dif_pos hiS] using hlo)

def canonicalLottery (ξ : ℝ) (c : ℕ) (b : ι→ℝ) : FiniteLaw (Finset ι) :=
  ExactCapacity.symmetricLottery (positiveMarginal ξ c b)

theorem canonicalLottery_implements {ξ : ℝ} (hξ : 0<ξ) (hξ1 : ξ<1) (c : ℕ) (b : ι→ℝ) :
    ExactCapacity.Implements (positiveMarginal ξ c b) (min c (positiveSupport b).card)
      (canonicalLottery ξ c b) := by
  have hp := positiveMarginal_spec ξ c hξ hξ1 b
  exact ExactCapacity.symmetricLottery_implements _ _ hp.1 hp.2.1 hp.2.2

theorem canonicalLottery_bestResponse {ξ : ℝ} (hξ : 0<ξ) (hξ1 : ξ<1) (c : ℕ) (b : ι→ℝ)
    (ν : FiniteLaw (Finset ι)) (hν : ∀S,ν.mass S≠0→S.card≤c) :
    ClippedResidual.revenueAgainst ξ b ν (canonicalLottery ξ c b)≤
      ClippedResidual.revenueAgainst ξ b (canonicalLottery ξ c b) (canonicalLottery ξ c b) := by
  have hp := positiveMarginal_spec ξ c hξ hξ1 b
  have hm := canonicalLottery_implements hξ hξ1 c b
  obtain ⟨z,hz,ht,hslack⟩ := positiveMarginal_threshold hξ hξ1 c b
  let p := positiveMarginal ξ c b
  let q := Proposer.marginal ν
  let r := fun i=>b i*(1-ξ*p i)
  have hcoord : ∑i,(q i-p i)*(r i-z)≤0 :=
    Finset.sum_nonpos (fun i _=>Proposer.coordinate_threshold p r z hp.1 hp.2.1 ht i (q i)
      (ν.prob_nonneg _) (ν.prob_le_one _))
  have he : (∑i,(q i-p i)*(r i-z))=
      (∑i,q i*r i)-(∑i,p i*r i)-z*((∑i,q i)-(∑i,p i)) := by
    simp only [sub_mul,mul_sub,Finset.sum_sub_distrib,←Finset.sum_mul]
    ring
  have hcap : (∑i,q i)≤(c:ℝ) := Proposer.marginal_capacity ν c hν
  have hg : z*((∑i,q i)-(∑i,p i))≤0 := by
    have hh := mul_le_mul_of_nonneg_left (sub_le_sub_right hcap (∑i,p i)) hz
    exact hh.trans (le_of_eq hslack)
  rw [ClippedResidual.revenueAgainst_eq,ClippedResidual.revenueAgainst_eq,
    Proposer.revenue_marginals,Proposer.revenue_marginals]
  simp only [Proposer.marginal,hm.2]
  change (∑i,q i*r i)≤∑i,p i*r i
  linarith

theorem canonicalLottery_support_optimal {ξ : ℝ} (hξ : 0<ξ) (hξ1 : ξ<1)
    (c : ℕ) (b : ι→ℝ) :
    ∀S,(canonicalLottery ξ c b).mass S≠0→
      Finite.Optimal c (fun i=>b i*(1-ξ*positiveMarginal ξ c b i)) S := by
  have hm := canonicalLottery_implements hξ hξ1 c b
  apply CommonList.support_optimal c _ (canonicalLottery ξ c b)
    (fun S hS=>(hm.1 S hS).le.trans (min_le_left _ _))
  intro ν hν
  have hh := canonicalLottery_bestResponse hξ hξ1 c b ν hν
  rw [ClippedResidual.revenueAgainst_eq,ClippedResidual.revenueAgainst_eq] at hh
  simpa only [Proposer.marginal,hm.2] using hh

end FCAppendix.Affine.EqualCapacity
