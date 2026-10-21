import FCAppendix.Affine.Hybrid.FavoredNoisyPayoff

noncomputable section
namespace FCAppendix.Affine.Hybrid
open Set Filter Topology
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def rankTransfer (b : ι→ℝ) (i : ι) (y : ℝ) (j : ι) : ℝ :=
  rankScore (Function.update b i y) i j-rankScore b i j

omit [Fintype ι] in
lemma rankTransfer_self (b : ι→ℝ) (i : ι) (y : ℝ) : rankTransfer b i y i=0 := by
  simp [rankTransfer,rankScore]

lemma averageRank_update (b : ι→ℝ) (i : ι) (y : ℝ) (t : ι) :
    averageRank (Function.update b i y) t-averageRank b t=
      (if t=i then ∑j,rankTransfer b i y j else 0)-rankTransfer b i y t := by
  by_cases ht : t=i
  · subst t
    rw [rankTransfer_self]
    simp only [if_true,sub_zero,averageRank]
    rw [add_sub_add_left_eq_sub,←Finset.sum_sub_distrib]
    rfl
  · have hpoint (j : ι) : rankScore (Function.update b i y) t j-rankScore b t j=
        if j=i then -rankTransfer b i y t else 0 := by
      by_cases hj : j=i
      · subst j
        rw [if_pos rfl]
        have h1:=rankScore_add_reverse (Function.update b i y) i t
        have h0:=rankScore_add_reverse b i t
        unfold rankTransfer
        linarith
      · simp [rankScore,Function.update_of_ne ht,hj]
    simp only [if_neg ht,zero_sub,averageRank]
    rw [add_sub_add_left_eq_sub,←Finset.sum_sub_distrib]
    simp_rw [hpoint]
    simp

theorem rankLaw_update_expect [Nonempty ι] (b : ι→ℝ) (i : ι) (y : ℝ) (f : ι→ℝ) :
    (rankLaw (Function.update b i y)).expect f-(rankLaw b).expect f=
      (∑j,rankTransfer b i y j*(f i-f j))/rankDenominator ι := by
  have hsum : (∑t,(averageRank (Function.update b i y) t-averageRank b t)*f t)=
      ∑j,rankTransfer b i y j*(f i-f j) := by
    simp_rw [averageRank_update,sub_mul]
    rw [Finset.sum_sub_distrib]
    have hfirst : (∑t,(if t=i then ∑j,rankTransfer b i y j else 0)*f t)=
        (∑j,rankTransfer b i y j)*f i := by simp [ite_mul]
    rw [hfirst,Finset.sum_mul]
    simp only [mul_sub,Finset.sum_sub_distrib]
  unfold FiniteLaw.expect rankLaw
  change (∑t,averageRank (Function.update b i y) t/rankDenominator ι*f t)-
    (∑t,averageRank b t/rankDenominator ι*f t)=_
  simp_rw [div_mul_eq_mul_div]
  rw [←Finset.sum_div,←Finset.sum_div,←sub_div,←Finset.sum_sub_distrib]
  have he : (∑t,(averageRank (Function.update b i y) t*f t-averageRank b t*f t))=
      ∑t,(averageRank (Function.update b i y) t-averageRank b t)*f t := by
    apply Finset.sum_congr rfl
    intro t _
    ring
  rw [he,hsum]

omit [Fintype ι] in
lemma rankTransfer_nonneg (b : ι→ℝ) (i j : ι) (y : ℝ) (hy : b i≤y) :
    0≤rankTransfer b i y j := by
  by_cases hji : j=i
  · subst j;rw [rankTransfer_self]
  · unfold rankTransfer rankScore
    simp only [Function.update_self,Function.update_of_ne hji]
    split_ifs <;> linarith

omit [Fintype ι] in
lemma rankTransfer_eq_zero_of_not_between (b : ι→ℝ) (i j : ι) (y : ℝ)
    (hy : b i≤y) (hout : b j∉Icc (b i) y) : rankTransfer b i y j=0 := by
  by_cases hji : j=i
  · subst j;exact rankTransfer_self b i y
  · have hh : b j<b i ∨ y<b j := by simpa only [mem_Icc,not_and_or,not_le] using hout
    rcases hh with hlo | hhi
    · have hh:=hlo.trans_le hy
      simp [rankTransfer,rankScore,hji,hlo,hh]
    · have hh:=hy.trans_lt hhi
      simp [rankTransfer,rankScore,hji,hhi,hh,not_lt_of_ge hhi.le,not_lt_of_ge hh.le]

omit [Fintype ι] in
lemma rankTransfer_half_le_between (b : ι→ℝ) (i j : ι) (y : ℝ)
    (hji : j≠i) (hy : b i<y) (hin : b j∈Icc (b i) y) :
    (1/2:ℝ)≤rankTransfer b i y j := by
  unfold rankTransfer rankScore
  simp only [Function.update_self,Function.update_of_ne hji]
  split_ifs <;> linarith [hin.1,hin.2]

lemma abs_expect_sub_expect_le {Ω : Type*} [Fintype Ω] (P : FiniteLaw Ω)
    (f g : Ω→ℝ) (C : ℝ) (h : ∀t,|f t-g t|≤C) : |P.expect f-P.expect g|≤C := by
  rw [←FiniteLaw.expect_sub]
  unfold FiniteLaw.expect
  calc
    _ ≤ ∑t,|P.mass t*(f t-g t)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑t,P.mass t*|f t-g t| := by
      apply Finset.sum_congr rfl
      intro t _
      rw [abs_mul,abs_of_nonneg (P.nonneg t)]
    _ ≤ ∑t,P.mass t*C := Finset.sum_le_sum (fun t _=>mul_le_mul_of_nonneg_left (h t) (P.nonneg t))
    _ = C := by rw [←Finset.sum_mul,P.total,one_mul]

end FCAppendix.Affine.Hybrid
