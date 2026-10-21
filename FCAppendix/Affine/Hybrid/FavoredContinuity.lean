import FCAppendix.Affine.Hybrid.OwnerLaw

noncomputable section
namespace FCAppendix.Affine.Hybrid
open Filter Topology
open scoped BigOperators

variable {ι X : Type*} [Fintype ι] [TopologicalSpace X]

def rankPairPayoff (b : X → ι → ℝ) (f : ι → X → ℝ) (i j : ι) (x : X) : ℝ :=
  rankScore (b x) i j*f i x+rankScore (b x) j i*f j x

omit [Fintype ι] [TopologicalSpace X] in
lemma rankPairPayoff_at_equal_payoff (b : X → ι → ℝ) (f : ι → X → ℝ)
    (i j : ι) (x : X) (heq : f i x=f j x) : rankPairPayoff b f i j x=f i x := by
  unfold rankPairPayoff
  rw [←heq,←add_mul,rankScore_add_reverse,one_mul]

omit [Fintype ι] [TopologicalSpace X] in
lemma rankPairPayoff_error (b : X → ι → ℝ) (f : ι → X → ℝ)
    (i j : ι) (x : X) (v : ℝ) :
    |rankPairPayoff b f i j x-v| ≤ |f i x-v|+|f j x-v| := by
  have hsum := rankScore_add_reverse (b x) i j
  have h₁ := rankScore_bounds (b x) i j
  have h₂ := rankScore_bounds (b x) j i
  have he : rankPairPayoff b f i j x-v=
      rankScore (b x) i j*(f i x-v)+rankScore (b x) j i*(f j x-v) := by
    unfold rankPairPayoff
    linear_combination v*hsum
  rw [he]
  calc
    _ ≤ |rankScore (b x) i j*(f i x-v)|+|rankScore (b x) j i*(f j x-v)| := abs_add_le _ _
    _ = rankScore (b x) i j*|f i x-v|+rankScore (b x) j i*|f j x-v| := by
      rw [abs_mul,abs_mul,abs_of_nonneg h₁.1,abs_of_nonneg h₂.1]
    _ ≤ _ := add_le_add
      (mul_le_of_le_one_left (abs_nonneg _) h₁.2)
      (mul_le_of_le_one_left (abs_nonneg _) h₂.2)

omit [Fintype ι] in
lemma continuousAt_rankPairPayoff {b : X → ι → ℝ} {f : ι → X → ℝ} {x : X} (i j : ι)
    (hbi : ContinuousAt (fun x=>b x i) x) (hbj : ContinuousAt (fun x=>b x j) x)
    (hfi : ContinuousAt (f i) x) (hfj : ContinuousAt (f j) x)
    (htie : b x i=b x j → f i x=f j x) :
    ContinuousAt (rankPairPayoff b f i j) x := by
  rcases lt_trichotomy (b x i) (b x j) with hlt | heq | hgt
  · apply hfj.congr_of_eventuallyEq
    filter_upwards [hbi.eventually_lt hbj hlt] with y hy
    simp [rankPairPayoff,rankScore,hy,not_lt_of_ge hy.le]
  · have hval := rankPairPayoff_at_equal_payoff b f i j x (htie heq)
    rw [Metric.continuousAt_iff']
    intro ε hε
    have hi := (Metric.continuousAt_iff'.mp hfi) (ε/2) (by linarith)
    have hj := (Metric.continuousAt_iff'.mp hfj) (ε/2) (by linarith)
    filter_upwards [hi,hj] with y hyi hyj
    rw [Real.dist_eq,hval]
    have herr := rankPairPayoff_error b f i j y (f i x)
    rw [Real.dist_eq] at hyi hyj
    rw [←htie heq] at hyj
    exact herr.trans_lt (by linarith)
  · apply hfi.congr_of_eventuallyEq
    filter_upwards [hbj.eventually_lt hbi hgt] with y hy
    simp [rankPairPayoff,rankScore,hy,not_lt_of_ge hy.le]

lemma rankPayoff_pair_identity (b : ι → ℝ) (f : ι → ℝ) :
    ∑ i,averageRank b i*f i=
      ((∑i,f i)+∑i,∑j,(rankScore b i j*f i+rankScore b j i*f j))/2 := by
  have hsym : (∑i,∑j,rankScore b j i*f j)=(∑i,∑j,rankScore b i j*f i) :=
    Finset.sum_comm
  simp only [averageRank,add_mul,Finset.sum_add_distrib,Finset.sum_mul]
  rw [hsym]
  simp only [←Finset.mul_sum]
  ring

theorem continuousAt_rankLaw_expect [Nonempty ι]
    {b : X → ι → ℝ} {f : ι → X → ℝ} {x : X}
    (hb : ∀ i,ContinuousAt (fun x=>b x i) x) (hf : ∀ i,ContinuousAt (f i) x)
    (htie : ∀ i j,b x i=b x j → f i x=f j x) :
    ContinuousAt (fun y=>(rankLaw (b y)).expect (fun i=>f i y)) x := by
  have he (y : X) : (rankLaw (b y)).expect (fun i=>f i y)=
      (((∑i,f i y)+∑i,∑j,rankPairPayoff b f i j y)/2)/rankDenominator ι := by
    calc
      _ = (∑i,averageRank (b y) i*f i y)/rankDenominator ι := by
        unfold FiniteLaw.expect rankLaw
        simp only
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by rw [rankPayoff_pair_identity]; rfl
  simp_rw [he]
  have hsum : ContinuousAt (fun y=>∑i,f i y) x :=
    tendsto_finsetSum _ (fun i _=>hf i)
  have hpairs : ContinuousAt (fun y=>∑i,∑j,rankPairPayoff b f i j y) x :=
    tendsto_finsetSum _ (fun i _=>tendsto_finsetSum _
      (fun j _=>continuousAt_rankPairPayoff i j (hb i) (hb j) (hf i) (hf j) (htie i j)))
  exact ((hsum.add hpairs).div_const 2).div_const _

end FCAppendix.Affine.Hybrid
