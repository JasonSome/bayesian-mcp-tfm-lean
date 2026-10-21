import FCAppendix.Affine.UniformFinite.SourceGuards
import FCAppendix.Affine.EqualCapacityLottery
import FCAppendix.Affine.EqualCapacityBoundary
import FCAppendix.Proposer.CommonListGame

noncomputable section
namespace FCAppendix.Affine.UniformFinite
open Set MeasureTheory ProbabilityTheory Filter Topology Classical
open scoped BigOperators

abbrev Allocation (M : ℕ) := Finset (Fin M)×Finset (Fin M)

def orient {M : ℕ} (row : Source.CountRow M) (P : Allocation M) : Allocation M :=
  if Source.residual row 0< Source.residual row 1 then (P.2,P.1) else P

lemma orient_success {M : ℕ} (row : Source.CountRow M) (j : Fin M) (P : Allocation M) :
    Literal.firstCopy j (orient row P)=Literal.firstCopy j P := by
  unfold orient Literal.firstCopy
  split_ifs <;> ring

lemma orient_duplicate {M : ℕ} (row : Source.CountRow M) (j : Fin M) (P : Allocation M) :
    Literal.duplicateCopy j (orient row P)=Literal.duplicateCopy j P := by
  unfold orient Literal.duplicateCopy
  split_ifs <;> ring

def canonicalLaw {M : ℕ} [NeZero M] (i : Uniform07.Row)
    (G : Uniform05.RestrictedLaw i) (row : Source.CountRow M) (b : Fin M→ℝ) :
    FiniteLaw (Allocation M) :=
  (Literal.weightedExperiment (Uniform05.xi i) (Source.rootLo i G) (Source.rootHi i G)
    (Source.lowerBids row b) (Source.sourceWeights i G row b)
    (Source.small row) (Source.imbalance row)).map (fun x=> orient row x.2)

def equalLottery {M : ℕ} (i : Uniform07.Row) (row : Source.CountRow M)
    (b : Fin M→ℝ) : FiniteLaw (Finset (Fin M)) :=
  ExactCapacity.symmetricLottery
    (EqualCapacity.positiveMarginal (Uniform05.xi i) (Source.small row) (Source.lowerBids row b))

def equalLaw {M : ℕ} (i : Uniform07.Row) (row : Source.CountRow M)
    (b : Fin M→ℝ) : FiniteLaw (Allocation M) :=
  (equalLottery i row b).prod (equalLottery i row b)

def pureLaw {M : ℕ} (i : Uniform07.Row) (row : Source.CountRow M)
    (b : Fin M→ℝ) : FiniteLaw (Allocation M) :=
  FiniteLaw.dirac ((Source.lowerTemplate row).selection (Uniform05.kappa i) (Source.lowerBids row b))

def continuationLaw {M : ℕ} [NeZero M] (i : Uniform07.Row)
    (G : Uniform05.RestrictedLaw i) (row : Source.CountRow M) (b : Fin M→ℝ) :
    FiniteLaw (Allocation M) :=
  if Source.residual row 0=Source.residual row 1 then equalLaw i row b
  else FiniteLaw.mixture (canonicalLaw i G row b) (pureLaw i row b)
    (Source.guardAlpha i G row b)
    (Source.guardAlpha_bounds i G row b).1 (Source.guardAlpha_bounds i G row b).2

def pairPayoff {M : ℕ} (eta v own : ℝ) (focal : Fin M) (P : Allocation M) : ℝ :=
  (v-own)*Literal.firstCopy focal P-eta*own*Literal.duplicateCopy focal P

def rowPayoff {M : ℕ} [NeZero M] (i : Uniform07.Row)
    (G : Uniform05.RestrictedLaw i) (row : Source.CountRow M)
    (v : ℝ) (b : Fin M→ℝ) (focal : Fin M) : ℝ :=
  (continuationLaw i G row b).expect (pairPayoff (Uniform05.eta i) v (b focal) focal)

def successProbability {M : ℕ} [NeZero M] (i : Uniform07.Row)
    (G : Uniform05.RestrictedLaw i) (row : Source.CountRow M)
    (b : Fin M→ℝ) (focal : Fin M) : ℝ :=
  (continuationLaw i G row b).expect (Literal.firstCopy focal)

def duplicateProbability {M : ℕ} [NeZero M] (i : Uniform07.Row)
    (G : Uniform05.RestrictedLaw i) (row : Source.CountRow M)
    (b : Fin M→ℝ) (focal : Fin M) : ℝ :=
  (continuationLaw i G row b).expect (Literal.duplicateCopy focal)

lemma pairPayoff_bound {M : ℕ} (eta v own : ℝ) (focal : Fin M) (P : Allocation M) :
    |pairPayoff eta v own focal P|≤|v|+(1+|eta|)*|own| := by
  classical
  unfold pairPayoff Literal.firstCopy Literal.duplicateCopy WeightedSampling.indicator
  by_cases h0 : focal∈P.1 <;> by_cases h1 : focal∈P.2 <;>
    simp only [h0,h1,if_true,if_false,mul_one,mul_zero,sub_zero,
      one_add_one_eq_two,add_zero,zero_add,
      show (2:ℝ)-1=1 by norm_num,show (0:ℝ)-0=0 by norm_num,abs_zero]
  · calc
      |v-own-eta*own|≤|v-own|+|eta*own| := abs_sub _ _
      _≤(|v|+|own|)+|eta| *|own| := by
        rw [abs_mul]
        have h := abs_sub v own
        linarith
      _=|v|+(1+|eta|)*|own| := by ring
  · exact (abs_sub _ _).trans (by nlinarith [mul_nonneg (abs_nonneg eta) (abs_nonneg own)])
  · exact (abs_sub _ _).trans (by nlinarith [mul_nonneg (abs_nonneg eta) (abs_nonneg own)])
  · positivity

lemma rowPayoff_bound {M : ℕ} [NeZero M] (i : Uniform07.Row)
    (G : Uniform05.RestrictedLaw i) (row : Source.CountRow M)
    (v : ℝ) (b : Fin M→ℝ) (focal : Fin M) :
    |rowPayoff i G row v b focal|≤|v|+(1+|Uniform05.eta i|)*|b focal| := by
  unfold rowPayoff
  apply abs_le.mpr
  constructor
  · apply FiniteLaw.const_le_expect
    intro P
    exact (abs_le.mp (pairPayoff_bound _ _ _ _ P)).1
  · apply FiniteLaw.expect_le_const
    intro P
    exact (abs_le.mp (pairPayoff_bound _ _ _ _ P)).2

lemma rowPayoff_success_duplicate {M : ℕ} [NeZero M] (i : Uniform07.Row)
    (G : Uniform05.RestrictedLaw i) (row : Source.CountRow M)
    (v : ℝ) (b : Fin M→ℝ) (focal : Fin M) :
    rowPayoff i G row v b focal=(v-b focal)*successProbability i G row b focal-
      Uniform05.eta i*b focal*duplicateProbability i G row b focal := by
  unfold rowPayoff pairPayoff successProbability duplicateProbability
  rw [FiniteLaw.expect_sub,FiniteLaw.expect_const_mul,FiniteLaw.expect_const_mul]

lemma continuation_equal {M : ℕ} [NeZero M] (i : Uniform07.Row)
    (G : Uniform05.RestrictedLaw i) (row : Source.CountRow M) (b : Fin M→ℝ)
    (he : Source.residual row 0=Source.residual row 1) :
    continuationLaw i G row b=equalLaw i row b := by
  simp only [continuationLaw,if_pos he]

lemma continuation_alpha_zero {M : ℕ} [NeZero M] (i : Uniform07.Row)
    (G : Uniform05.RestrictedLaw i) (row : Source.CountRow M) (b : Fin M→ℝ)
    (he : Source.residual row 0≠Source.residual row 1)
    (ha : Source.guardAlpha i G row b=0) :
    continuationLaw i G row b=pureLaw i row b := by
  apply FiniteLaw.ext
  intro P
  simp [continuationLaw,he,FiniteLaw.mixture,ha]

theorem rowPayoff_unequal {M : ℕ} [NeZero M] (i : Uniform07.Row)
    (G : Uniform05.RestrictedLaw i) (row : Source.CountRow M)
    (v : ℝ) (b : Fin M→ℝ) (focal : Fin M)
    (he : Source.residual row 0≠Source.residual row 1) :
    rowPayoff i G row v b focal=
      Source.guardAlpha i G row b*
        (canonicalLaw i G row b).expect (pairPayoff (Uniform05.eta i) v (b focal) focal)+
      (1-Source.guardAlpha i G row b)*
        pairPayoff (Uniform05.eta i) v (b focal) focal
          ((Source.lowerTemplate row).selection (Uniform05.kappa i) (Source.lowerBids row b)) := by
  unfold rowPayoff continuationLaw
  rw [if_neg he,FiniteLaw.expect_mixture]
  simp only [pureLaw,FiniteLaw.expect_dirac]

def pairCount {M : ℕ} (focal : Fin M) (P : Allocation M) : Fin 3 :=
  if focal∈P.1∩P.2 then 2 else if focal∈P.1∪P.2 then 1 else 0

def rowCountLaw {M : ℕ} [NeZero M] (i : Uniform07.Row)
    (G : Uniform05.RestrictedLaw i) (row : Source.CountRow M)
    (b : Fin M→ℝ) (focal : Fin M) : FiniteLaw (Fin 3) :=
  (continuationLaw i G row b).map (pairCount focal)

theorem pairPayoff_overbid {M : ℕ} {eta v own : ℝ}
    (heta : 0≤ eta) (hv : 0≤ v) (hb : v< own) (focal : Fin M) (P : Allocation M) :
    pairPayoff eta v own focal P≤0 := by
  have hown : 0≤ own := hv.trans hb.le
  have hsuccess : 0≤ Literal.firstCopy focal P := by
    unfold Literal.firstCopy WeightedSampling.indicator
    split_ifs <;> norm_num
  have hduplicate : 0≤ Literal.duplicateCopy focal P := by
    unfold Literal.duplicateCopy WeightedSampling.indicator
    split_ifs <;> norm_num
  have hs := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hb.le) hsuccess
  have hd := mul_nonneg (mul_nonneg heta hown) hduplicate
  unfold pairPayoff
  linarith

end FCAppendix.Affine.UniformFinite
