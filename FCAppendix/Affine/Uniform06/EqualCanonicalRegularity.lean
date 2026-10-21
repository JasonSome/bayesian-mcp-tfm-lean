import FCAppendix.Affine.Uniform06.PrefixMonotonicity
import FCAppendix.Affine.Uniform06.PureRankSelector
import FCAppendix.Affine.Uniform06.LowChernoffRows
import FCAppendix.Affine.EqualCapacityBoundary

noncomputable section
namespace FCAppendix.Affine.Uniform06.EqualCanonicalRegularity

open MeasureTheory Set Filter
open scoped BigOperators
open LowBody PrefixMonotonicity PureRankSelector
open FCAppendix.Affine.ClippedResidual

section FiniteKernel
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem actual_marginal_increment
    {ξ x y : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (c : ℕ) (b : ι → ℝ) (i : ι)
    (hb : ∀ j, j ≠ i → 0 ≤ b j) (hx : 0 < x) (hxy : x ≤ y) :
    0 ≤ clippedMarginal ξ c b i y-clippedMarginal ξ c b i x ∧
      clippedMarginal ξ c b i y-clippedMarginal ξ c b i x ≤ (y-x)/(ξ*x) := by
  classical
  let b₀ := Function.update b i x
  let b₁ := Function.update b i y
  let p := EqualCapacity.positiveMarginal ξ c b₀
  let q := EqualCapacity.positiveMarginal ξ c b₁
  let d := q i-p i
  have hp := EqualCapacity.positiveMarginal_spec ξ c hξ hξ1 b₀
  have hq := EqualCapacity.positiveMarginal_spec ξ c hξ hξ1 b₁
  have hd : 0 ≤ d := sub_nonneg.mpr
    (LowBody.positiveMarginal_update_mono hξ hξ1 c b i hb hx.le hxy)
  have hb₀ (j : ι) : 0 ≤ b₀ j := by
    by_cases hj : j=i
    · simpa only [b₀,hj,Function.update_self] using hx.le
    · simpa only [b₀,Function.update_of_ne hj] using hb j hj
  have hcross := EqualCapacity.positive_kernel_cross hξ hξ1 c b₀ b₁
  change (∑ j, (q j-p j)*(b₀ j*(1-ξ*p j)-b₁ j*(1-ξ*q j))) ≤ 0 at hcross
  have hexpand : (∑ j, (q j-p j)*(b₀ j*(1-ξ*p j)-b₁ j*(1-ξ*q j))) =
      (∑ j, ξ*b₀ j*(q j-p j)^2)-
        ∑ j, (q j-p j)*(b₁ j-b₀ j)*(1-ξ*q j) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hsingle : (∑ j, (q j-p j)*(b₁ j-b₀ j)*(1-ξ*q j)) =
      d*(y-x)*(1-ξ*q i) := by
    rw [Finset.sum_eq_single i]
    · simp only [b₀,b₁,Function.update_self,d]
    · intro j _ hji
      simp only [b₀,b₁,Function.update_of_ne hji,sub_self,mul_zero,zero_mul]
    · intro hn
      exact False.elim (hn (Finset.mem_univ i))
  rw [hexpand,hsingle] at hcross
  have henergy : ξ*x*d^2 ≤ ∑ j, ξ*b₀ j*(q j-p j)^2 := by
    have hh := Finset.single_le_sum (s := Finset.univ)
      (f := fun j => ξ*b₀ j*(q j-p j)^2)
      (fun j _ => mul_nonneg (mul_nonneg hξ.le (hb₀ j)) (sq_nonneg _))
      (Finset.mem_univ i)
    simpa only [b₀,Function.update_self,d] using hh
  have hfactor : 1-ξ*q i ≤ 1 := by
    have hh := mul_nonneg hξ.le (hq.1 i)
    linarith
  have hprod : d*(y-x)*(1-ξ*q i) ≤ d*(y-x) :=
    mul_le_of_le_one_right (mul_nonneg hd (sub_nonneg.mpr hxy)) hfactor
  refine ⟨hd,?_⟩
  change d ≤ (y-x)/(ξ*x)
  apply (le_div_iff₀ (mul_pos hξ hx)).mpr
  by_cases hd0 : d=0
  · rw [hd0,zero_mul]
    exact sub_nonneg.mpr hxy
  · have hdpos : 0 < d := lt_of_le_of_ne hd (Ne.symm hd0)
    have hc : (d*(ξ*x))*d ≤ (y-x)*d := by nlinarith
    exact le_of_mul_le_mul_right hc hdpos

theorem actual_duplicate_increment
    {ξ x y : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (c : ℕ) (b : ι → ℝ) (i : ι)
    (hb : ∀ j, j ≠ i → 0 ≤ b j) (hx : 0 < x) (hxy : x ≤ y) :
    0 ≤ clippedDuplicate ξ c b i y-clippedDuplicate ξ c b i x ∧
      clippedDuplicate ξ c b i y-clippedDuplicate ξ c b i x ≤ 2*(y-x)/(ξ*x) := by
  have hm := actual_marginal_increment hξ hξ1 c b i hb hx hxy
  have hp := EqualCapacity.positiveMarginal_spec ξ c hξ hξ1 (Function.update b i x)
  have hq := EqualCapacity.positiveMarginal_spec ξ c hξ hξ1 (Function.update b i y)
  have hp0 : 0 ≤ clippedMarginal ξ c b i x := hp.1 i
  have hp1 : clippedMarginal ξ c b i x ≤ 1 := hp.2.1 i
  have hq0 : 0 ≤ clippedMarginal ξ c b i y := hq.1 i
  have hq1 : clippedMarginal ξ c b i y ≤ 1 := hq.2.1 i
  have hl := mul_nonneg hm.1 (add_nonneg hp0 hq0)
  have hu := mul_nonneg hm.1 (show 0 ≤ 2-clippedMarginal ξ c b i y-
    clippedMarginal ξ c b i x by linarith)
  unfold clippedDuplicate
  constructor
  · nlinarith
  · have he : 2*((y-x)/(ξ*x))=2*(y-x)/(ξ*x) := by ring
    rw [← he]
    nlinarith

theorem actual_duplicate_increment_with_indicator
    {ξ x y : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (c : ℕ) (b : ι → ℝ) (i : ι)
    (hb : ∀ j, j ≠ i → 0 ≤ b j) (hx : 0 < x) (hxy : x ≤ y) :
    clippedDuplicate ξ c b i y-clippedDuplicate ξ c b i x ≤
      if 0 < clippedMarginal ξ c b i y then 2*(y-x)/(ξ*x) else 0 := by
  by_cases hy : 0 < clippedMarginal ξ c b i y
  · rw [if_pos hy]
    exact (actual_duplicate_increment hξ hξ1 c b i hb hx hxy).2
  · rw [if_neg hy]
    have hm := actual_marginal_increment hξ hξ1 c b i hb hx hxy
    have hp := EqualCapacity.positiveMarginal_spec ξ c hξ hξ1 (Function.update b i x)
    have hq := EqualCapacity.positiveMarginal_spec ξ c hξ hξ1 (Function.update b i y)
    have heq : clippedMarginal ξ c b i y=0 := le_antisymm (le_of_not_gt hy) (hq.1 i)
    have hep : clippedMarginal ξ c b i x=0 := by
      apply le_antisymm _ (hp.1 i)
      change clippedMarginal ξ c b i x ≤ 0
      have hpx : 0 ≤ clippedMarginal ξ c b i x := hp.1 i
      linarith
    simp [clippedDuplicate,heq,hep]

end FiniteKernel

section Threshold

theorem exposure_le_of_scalar_threshold
    {ξ b p L z : ℝ} (hξ : 0 < ξ) (hz : 0 < z) (hLz : L ≤ z)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hzero : p=0 → b*(1-ξ*p) ≤ L)
    (hinterior : 0 < p → p < 1 → b*(1-ξ*p)=L) : exposure ξ z b ≤ p := by
  by_cases hb : b ≤ z
  · rw [exposure_zero hb]
    exact hp0
  · have hzb := lt_of_not_ge hb
    have hb0 := hz.trans hzb
    by_cases hp : p=1
    · rw [hp]
      exact exposure_le_one _ _ _
    · have hp01 : p < 1 := lt_of_le_of_ne hp1 hp
      have hpPos : 0 < p := by
        by_contra h
        have hpEq : p=0 := le_antisymm (le_of_not_gt h) hp0
        have hh := hzero hpEq
        simp only [hpEq,mul_zero,sub_zero,mul_one] at hh
        linarith
      have hrec := hinterior hpPos hp01
      unfold exposure
      rw [max_eq_left hzb.le,max_eq_right (sub_nonneg.mpr hzb.le)]
      apply (min_le_right _ _).trans
      apply (div_le_iff₀ (mul_pos hξ hb0)).mpr
      nlinarith

theorem positive_focal_multiplier_lt_bid
    {ξ b p L : ℝ} (hξ : 0 < ξ) (hb : 0 < b) (hp : 0 < p) (hp1 : p ≤ 1)
    (hone : p=1 → L ≤ b*(1-ξ*p))
    (hinterior : 0 < p → p < 1 → b*(1-ξ*p)=L) : L < b := by
  have hd := mul_pos hb (mul_pos hξ hp)
  by_cases hpEq : p=1
  · have hh := hone hpEq
    nlinarith
  · have hh := hinterior hp (lt_of_le_of_ne hp1 hpEq)
    nlinarith

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem actual_rival_exposures_le_marginals
    {ξ z : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1) (hz : 0 < z)
    (c : ℕ) (b : ι → ℝ) (i : ι) (hbi : 0 < b i) (hib : b i ≤ z)
    (hpos : 0 < EqualCapacity.positiveMarginal ξ c b i) :
    ∀ j, exposure ξ z (b j) ≤ EqualCapacity.positiveMarginal ξ c b j := by
  let p := EqualCapacity.positiveMarginal ξ c b
  have hp := EqualCapacity.positiveMarginal_spec ξ c hξ hξ1 b
  obtain ⟨L,hL,hT,hslack⟩ := EqualCapacity.positiveMarginal_threshold hξ hξ1 c b
  have hLi := positive_focal_multiplier_lt_bid hξ hbi hpos (hp.2.1 i)
    (hT.2.1 i) (hT.2.2 i)
  intro j
  exact exposure_le_of_scalar_threshold hξ hz (hLi.le.trans hib)
    (hp.1 j) (hp.2.1 j) (hT.1 j) (hT.2.2 j)

end Threshold

section ActualRow
variable {N : ℕ}

def equalMarginal (ξ : ℝ) (c : ℕ) (b : ℝ) (ω : Fin N → RowRival) : ℝ :=
  EqualCapacity.positiveMarginal ξ (rowResidual c 0 ω) (rowBids b ω) 0

def equalDuplicate (ξ : ℝ) (c : ℕ) (b : ℝ) (ω : Fin N → RowRival) : ℝ :=
  if rowResidual c 0 ω=rowResidual c 1 ω then (equalMarginal ξ c b ω)^2 else 0

def rivalStatistic (ξ z : ℝ) (r : RowRival) : ℝ :=
  if r.1=0 then exposure ξ z r.2 else 1/2

theorem equalMarginal_increment
    {ξ x y : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (c : ℕ) (ω : Fin N → RowRival)
    (hω : ∀ j, (ω j).1=0 → 0 ≤ (ω j).2) (hx : 0 < x) (hxy : x ≤ y) :
    0 ≤ equalMarginal ξ c y ω-equalMarginal ξ c x ω ∧
      equalMarginal ξ c y ω-equalMarginal ξ c x ω ≤ (y-x)/(ξ*x) := by
  have hb : ∀ j : Fin (N+1), j ≠ 0 → 0 ≤ rowBids x ω j :=
    fun j _ => rowBids_nonneg x ω hx.le hω j
  have hh := actual_marginal_increment hξ hξ1 (rowResidual c 0 ω)
    (rowBids x ω) 0 hb hx hxy
  simpa only [clippedMarginal, rowBids_update, equalMarginal] using hh

theorem exposure_zero_bid (ξ z : ℝ) : exposure ξ z 0 = 0 := by
  by_cases hz : 0 ≤ z
  · exact exposure_zero hz
  · have hz' : z ≤ 0 := le_of_not_ge hz
    simp [exposure,max_eq_left hz']

theorem row_exposure_sum (ξ z : ℝ) (ω : Fin N → RowRival)
    (hno : ∀ j, (ω j).1 ≠ 1) :
    (∑ j, rivalStatistic ξ z (ω j)) =
      (∑ j : Fin N, exposure ξ z (rowBids (0:ℝ) ω j.succ))+
        ((classCount 2 ω:ℝ)+classCount 3 ω)/2 := by
  classical
  have hterm (j : Fin N) : rivalStatistic ξ z (ω j) =
      exposure ξ z (rowBids (0:ℝ) ω j.succ)+
        ((if (ω j).1=2 then (1:ℝ) else 0)+
          (if (ω j).1=3 then (1:ℝ) else 0))/2 := by
    simp only [rowBids,Fin.cons_succ]
    have hj := hno j
    generalize hk : (ω j).1=k at *
    fin_cases k <;>
      simp_all [rivalStatistic,exposure_zero_bid]
  calc
    (∑ j, rivalStatistic ξ z (ω j)) =
        ∑ j, (exposure ξ z (rowBids (0:ℝ) ω j.succ)+
          ((if (ω j).1=2 then (1:ℝ) else 0)+
            (if (ω j).1=3 then (1:ℝ) else 0))/2) :=
      Finset.sum_congr rfl (fun j _ => hterm j)
    _ = _ := by
      simp only [classCount,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
      rw [Finset.sum_add_distrib]
      congr 1
      calc
        _ = (∑ j : Fin N, ((if (ω j).1=2 then (1:ℝ) else 0) +
            (if (ω j).1=3 then (1:ℝ) else 0)))/2 := by
          rw [Finset.sum_div]
        _ = _ := by rw [Finset.sum_add_distrib]

theorem equal_positive_implies_scalar_tail
    {ξ z b : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1) (hz : 0 < z)
    (c : ℕ) (ω : Fin N → RowRival) (hb : 0 < b) (hbz : b ≤ z)
    (hno : ∀ j, (ω j).1 ≠ 1)
    (hequal : rowResidual c 0 ω=rowResidual c 1 ω)
    (hpos : 0 < equalMarginal ξ c b ω) :
    (∑ j, rivalStatistic ξ z (ω j)) < c := by
  let r := rowResidual c 0 ω
  let p := EqualCapacity.positiveMarginal ξ r (rowBids b ω)
  have hp := EqualCapacity.positiveMarginal_spec ξ r hξ hξ1 (rowBids b ω)
  have hsum : (∑ j, p j) ≤ (r:ℝ) :=
    hp.2.2.le.trans (Nat.cast_le.mpr (min_le_left _ _))
  have hpr : 0 < r := by
    have hself := Finset.single_le_sum (s := Finset.univ) (f := p)
      (fun j _ => hp.1 j) (Finset.mem_univ 0)
    have hh : (0:ℝ) < r := hpos.trans_le (hself.trans hsum)
    exact Nat.cast_pos.mp hh
  have hpr1 : 0 < rowResidual c 1 ω := by rwa [← hequal]
  have hc1 := no_active_count_zero ω hno
  have hr0 : r ≤ c-classCount 2 ω := by
    dsimp [r]
    convert! (min_le_right (1+classCount 0 ω) (c-classCount 2 ω)) using 1
    simp only [rowResidual,hc1,Nat.sub_zero]
    rfl

  have hr1 : r ≤ c-classCount 3 ω := by
    dsimp only [r]
    rw [hequal]
    convert! (min_le_right (1+classCount 0 ω) (c-classCount 3 ω)) using 1
    simp only [rowResidual,hc1,Nat.sub_zero]
    rfl
  have hC2 : classCount 2 ω ≤ c := by omega
  have hC3 : classCount 3 ω ≤ c := by omega
  have hr0R : (r:ℝ)+(classCount 2 ω:ℝ) ≤ c := by exact_mod_cast (show r+classCount 2 ω ≤ c by omega)
  have hr1R : (r:ℝ)+(classCount 3 ω:ℝ) ≤ c := by exact_mod_cast (show r+classCount 3 ω ≤ c by omega)
  have hdom := actual_rival_exposures_le_marginals hξ hξ1 hz r (rowBids b ω)
    0 (by simpa only [rowBids,Fin.cons_zero] using hb)
    (by simpa only [rowBids,Fin.cons_zero] using hbz) hpos
  have hrest : (∑ j : Fin N, exposure ξ z (rowBids (0:ℝ) ω j.succ)) ≤
      ∑ j : Fin N, p j.succ := by
    apply Finset.sum_le_sum
    intro j _
    exact hdom j.succ
  rw [Fin.sum_univ_succ] at hsum
  rw [row_exposure_sum ξ z ω hno]
  change 0 < p 0 at hpos
  nlinarith

theorem equal_duplicate_increment_with_tail
    {ξ z x y : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1) (hz : 0 < z)
    (c : ℕ) (ω : Fin N → RowRival)
    (hω : ∀ j, (ω j).1=0 → 0 ≤ (ω j).2)
    (hno : ∀ j, (ω j).1 ≠ 1) (hx : 0 < x) (hxy : x ≤ y) (hyz : y ≤ z) :
    equalDuplicate ξ c y ω-equalDuplicate ξ c x ω ≤
      if (∑ j, rivalStatistic ξ z (ω j)) < c then 2*(y-x)/(ξ*x) else 0 := by
  by_cases heq : rowResidual c 0 ω=rowResidual c 1 ω
  · have hbase := actual_duplicate_increment_with_indicator hξ hξ1
      (rowResidual c 0 ω) (rowBids x ω) 0
      (fun j _ => rowBids_nonneg x ω hx.le hω j) hx hxy
    have he (u : ℝ) : clippedDuplicate ξ (rowResidual c 0 ω) (rowBids x ω) 0 u =
        (equalMarginal ξ c u ω)^2 := by
      simp only [clippedDuplicate,clippedMarginal,rowBids_update,equalMarginal]
    rw [he y,he x] at hbase
    have hp : clippedMarginal ξ (rowResidual c 0 ω) (rowBids x ω) 0 y =
        equalMarginal ξ c y ω := by
      simp only [clippedMarginal,rowBids_update,equalMarginal]
    rw [hp] at hbase
    unfold equalDuplicate
    rw [if_pos heq,if_pos heq]
    by_cases hpy : 0 < equalMarginal ξ c y ω
    · rw [if_pos hpy] at hbase
      rw [if_pos (equal_positive_implies_scalar_tail hξ hξ1 hz c ω
        (hx.trans_le hxy) hyz hno heq hpy)]
      exact hbase
    · rw [if_neg hpy] at hbase
      apply hbase.trans
      split_ifs
      · positivity
      · exact le_rfl
  · simp only [equalDuplicate,if_neg heq,sub_self]
    split_ifs
    · positivity
    · exact le_rfl

end ActualRow

end FCAppendix.Affine.Uniform06.EqualCanonicalRegularity
