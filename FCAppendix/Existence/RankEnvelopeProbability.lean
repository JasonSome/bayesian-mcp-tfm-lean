import FCAppendix.Exclusive.NarrowExistenceGameScore
import FCAppendix.Probability.PiBinomial
import FCAppendix.Ample.RankMeasureTools

noncomputable section
namespace FCAppendix.Existence.RankEnvelope
open MeasureTheory Set Filter Topology
open Exclusive.Narrow Exclusive.Narrow.Existence
open scoped BigOperators

def rankSuccess (r c : ℕ) (p : ℝ) : ℝ :=
  binomialPolynomial r (fun k => if k<c then 1 else 0) p

theorem polynomial_forward_difference (n : ℕ) (f : ℕ → ℝ) (p : ℝ) :
    binomialPolynomialDerivative (n+1) f p =
      ((n+1:ℕ):ℝ)*binomialPolynomial n (fun k => f (1+k)-f k) p := by
  induction n generalizing f with
  | zero => simp only [binomialPolynomialDerivative,binomialPolynomial]; ring
  | succ n ih =>
    have hlin := binomialPolynomial_linear (n+1) (fun k => f (1+k)) f 1 (-1) p
    simp only [one_mul,neg_one_mul,← sub_eq_add_neg] at hlin
    calc
      _ = (binomialPolynomial (n+1) (fun k => f (1+k)) p-binomialPolynomial (n+1) f p)+
          ((n+1:ℕ):ℝ)*binomialPolynomial (n+1) (fun k => f (1+k)-f k) p := by
        rw [binomialPolynomialDerivative,ih,ih]
        simp only [binomialPolynomial]
        ring
      _ = _ := by rw [← hlin]; push_cast; ring

theorem rankSuccess_eq_prob (r c : ℕ) {p : ℝ} (hp : p ∈ Icc (0:ℝ) 1) :
    rankSuccess r c p = (IndependentCounts.binomial r p hp.1 hp.2).prob (fun k => k.val<c) := by
  rw [rankSuccess,binomialPolynomial_eq_expect r _ p hp.1 hp.2,FiniteLaw.prob_eq_expect]

theorem rankSuccess_bounds (r c : ℕ) {p : ℝ} (hp : p ∈ Icc (0:ℝ) 1) :
    rankSuccess r c p ∈ Icc (0:ℝ) 1 := by
  rw [rankSuccess_eq_prob r c hp]
  exact ⟨FiniteLaw.prob_nonneg _ _,FiniteLaw.prob_le_one _ _⟩

theorem continuous_rankSuccess (r c : ℕ) : Continuous (rankSuccess r c) := by
  exact continuous_iff_continuousAt.mpr fun p => (hasDerivAt_binomialPolynomial r _ p).continuousAt

theorem polynomial_singleton (r k : ℕ) {p : ℝ} (hp : p ∈ Icc (0:ℝ) 1) :
    binomialPolynomial r (fun j => if j=k then 1 else 0) p = PiBinomial.pmf r p k := by
  rw [binomialPolynomial_eq_expect r _ p hp.1 hp.2,← FiniteLaw.prob_eq_expect]
  by_cases hk : k ≤ r
  · have hm := PiBinomial.binomial_mass r p hp.1 hp.2 ⟨k,by omega⟩
    have he : (fun j : Fin (r+1) => j.val=k) = fun j => j=⟨k,by omega⟩ := by
      funext j
      simp only [Fin.ext_iff]
    rw [he,FiniteLaw.prob_eq_expect,FiniteLaw.expect_singleton,hm]
  · have hzero : (fun j : Fin (r+1) => j.val=k) = fun _ => False := by
      funext j
      apply propext
      constructor
      · intro hj
        have := j.isLt
        omega
      · exact False.elim
    rw [hzero,FiniteLaw.prob_false]
    simp only [PiBinomial.pmf,Nat.choose_eq_zero_of_lt (by omega : r<k),Nat.cast_zero,zero_mul]

theorem hasDerivAt_rankSuccess (r c : ℕ) (hc : 1 ≤ c) {p : ℝ} (hp : p ∈ Icc (0:ℝ) 1) :
    HasDerivAt (rankSuccess (r+1) c) (-((r+1:ℕ):ℝ)*PiBinomial.pmf r p (c-1)) p := by
  have he : (fun k : ℕ => (if 1+k<c then (1:ℝ) else 0)-(if k<c then 1 else 0)) =
      fun k => (-1)*(if k=c-1 then (1:ℝ) else 0)+0*(0:ℝ) := by
    funext k
    split_ifs <;> norm_num <;> omega
  have hder := hasDerivAt_binomialPolynomial (r+1) (fun k => if k<c then 1 else 0) p
  rw [polynomial_forward_difference,he,binomialPolynomial_linear,polynomial_singleton r (c-1) hp] at hder
  change HasDerivAt (binomialPolynomial (r+1) (fun k => if k<c then 1 else 0)) _ p
  simpa only [zero_mul,add_zero,neg_one_mul,mul_neg,one_mul,neg_mul] using hder

theorem pmf_pos {r k : ℕ} (hk : k ≤ r) {p : ℝ} (hp : p ∈ Ioo (0:ℝ) 1) :
    0 < PiBinomial.pmf r p k := by
  have hc : 0 < (r.choose k:ℝ) := by exact_mod_cast Nat.choose_pos hk
  exact mul_pos (mul_pos hc (pow_pos hp.1 _)) (pow_pos (sub_pos.mpr hp.2) _)

theorem strictAntiOn_rankSuccess (r c : ℕ) (hc : 1 ≤ c) (hcr : c ≤ r+1) :
    StrictAntiOn (rankSuccess (r+1) c) (Icc (0:ℝ) 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc (0:ℝ) 1) (continuous_rankSuccess _ _).continuousOn
  intro p hp
  rw [interior_Icc] at hp
  have hd := hasDerivAt_rankSuccess r c hc ⟨hp.1.le,hp.2.le⟩
  rw [hd.deriv]
  exact mul_neg_of_neg_of_pos (neg_neg_of_pos (by positivity)) (pmf_pos (by omega) hp)

theorem rankSuccess_pos (r c : ℕ) (hc : 1 ≤ c) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p < 1) : 0 < rankSuccess r c p := by
  have hprob := (IndependentCounts.binomial r p hp0 hp1.le).prob_mono
    (E:=fun j => j.val=0) (F:=fun j => j.val<c) (fun j hj => by omega)
  have hz := polynomial_singleton r 0 ⟨hp0,hp1.le⟩
  rw [binomialPolynomial_eq_expect r _ p hp0 hp1.le,← FiniteLaw.prob_eq_expect] at hz
  rw [rankSuccess_eq_prob r c ⟨hp0,hp1.le⟩]
  have hzero : 0 < (IndependentCounts.binomial r p hp0 hp1.le).prob (fun j => j.val=0) := by
    rw [hz]
    simpa only [PiBinomial.pmf,Nat.choose_zero_right,Nat.cast_one,pow_zero,Nat.sub_zero,one_mul]
      using pow_pos (sub_pos.mpr hp1) r
  exact hzero.trans_le hprob

theorem rankSuccess_zero (r c : ℕ) (hc : 1 ≤ c) : rankSuccess r c 0=1 := by
  unfold rankSuccess
  induction r with
  | zero => simp only [binomialPolynomial,if_pos (by omega : 0<c)]
  | succ r ih => simpa only [binomialPolynomial,sub_zero,one_mul,zero_mul,add_zero] using ih

def contactTail (mu : Measure ℝ) (n : ℕ) (v : ℝ) : ℝ := mu.real (Ioi v)/(n:ℝ)
def rank (mu : Measure ℝ) (r c n : ℕ) (v : ℝ) : ℝ := rankSuccess r c (contactTail mu n v)

theorem contactTail_bounds (mu : Measure ℝ) [IsFiniteMeasure mu] {n : ℕ}
    (hn : 2 ≤ n) (hmass : mu.real univ ≤ 1) (v : ℝ) :
    contactTail mu n v ∈ Ico (0:ℝ) 1 := by
  have hn0 : (0:ℝ)<n := by positivity
  have hn1 : (1:ℝ)<n := by exact_mod_cast hn
  have ht : mu.real (Ioi v) ≤ 1 := (measureReal_mono (subset_univ _)).trans hmass
  exact ⟨div_nonneg measureReal_nonneg hn0.le,(div_lt_one hn0).mpr (ht.trans_lt hn1)⟩

theorem rank_bounds (mu : Measure ℝ) [IsFiniteMeasure mu] (r c : ℕ) {n : ℕ}
    (hn : 2 ≤ n) (hmass : mu.real univ ≤ 1) (v : ℝ) : rank mu r c n v ∈ Icc (0:ℝ) 1 :=
  rankSuccess_bounds r c ⟨(contactTail_bounds mu hn hmass v).1,(contactTail_bounds mu hn hmass v).2.le⟩

theorem rank_pos (mu : Measure ℝ) [IsFiniteMeasure mu] (r c : ℕ) (hc : 1 ≤ c) {n : ℕ}
    (hn : 2 ≤ n) (hmass : mu.real univ ≤ 1) (v : ℝ) : 0 < rank mu r c n v :=
  rankSuccess_pos r c hc (contactTail_bounds mu hn hmass v).1 (contactTail_bounds mu hn hmass v).2

theorem continuous_rank (mu : Measure ℝ) [IsFiniteMeasure mu] [NullSingletonClass mu]
    (r c n : ℕ) : Continuous (rank mu r c n) :=
  (continuous_rankSuccess r c).comp
    ((Ample.RankMeasureTools.continuous_strict_tail mu (fun x => measure_singleton x)).div_const _)

theorem rank_monotone (mu : Measure ℝ) [IsFiniteMeasure mu] {r c n : ℕ}
    (hc : 1 ≤ c) (hcr : c ≤ r+1) (hn : 2 ≤ n) (hmass : mu.real univ ≤ 1) :
    Monotone (rank mu (r+1) c n) := by
  intro x v hxv
  have hn0 : (0:ℝ)<n := by positivity
  apply (strictAntiOn_rankSuccess r c hc hcr).antitoneOn
    ⟨(contactTail_bounds mu hn hmass v).1,(contactTail_bounds mu hn hmass v).2.le⟩
    ⟨(contactTail_bounds mu hn hmass x).1,(contactTail_bounds mu hn hmass x).2.le⟩
  exact div_le_div_of_nonneg_right (measureReal_mono (Ioi_subset_Ioi hxv)) hn0.le

theorem rank_strict_of_mass (mu : Measure ℝ) [IsFiniteMeasure mu] {r c n : ℕ}
    (hc : 1 ≤ c) (hcr : c ≤ r+1) (hn : 2 ≤ n) (hmass : mu.real univ ≤ 1)
    {x v : ℝ} (hxv : x<v) (hinterval : mu (Ioc x v) ≠ 0) :
    rank mu (r+1) c n x < rank mu (r+1) c n v := by
  have ht := Ample.RankMeasureTools.strict_tail_sub (μ:=mu) hxv.le
  have hm : 0 < mu.real (Ioc x v) :=
    ENNReal.toReal_pos hinterval (measure_ne_top _ _)
  apply (strictAntiOn_rankSuccess r c hc hcr)
    ⟨(contactTail_bounds mu hn hmass v).1,(contactTail_bounds mu hn hmass v).2.le⟩
    ⟨(contactTail_bounds mu hn hmass x).1,(contactTail_bounds mu hn hmass x).2.le⟩
  apply div_lt_div_of_pos_right _ (by positivity : (0:ℝ)<n)
  linarith

theorem rank_tendsto_one (mu : Measure ℝ) [IsFiniteMeasure mu] (r c n : ℕ) (hc : 1 ≤ c) :
    Tendsto (rank mu r c n) atTop (𝓝 1) := by
  have ht : Tendsto (fun v : ℝ => mu.real (Ioi v)) atTop (𝓝 0) := by
    simpa only [setIntegral_const,smul_eq_mul,mul_one,id_eq] using
      (tendsto_integral_Ioi_zero (f:=fun _ : ℝ => (1:ℝ)) (μ:=mu) tendsto_id)
  have hp := ht.div_const (n:ℝ)
  rw [zero_div] at hp
  have hq := (continuous_rankSuccess r c).continuousAt.tendsto.comp hp
  change Tendsto (fun v => rankSuccess r c (mu.real (Ioi v)/(n:ℝ))) atTop (𝓝 1)
  simpa only [Function.comp_def,rankSuccess_zero r c hc] using hq

end FCAppendix.Existence.RankEnvelope
