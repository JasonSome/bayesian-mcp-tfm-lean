import FCAppendix.Affine.Uniform06.PureRankCounts
import FCAppendix.Affine.Uniform06.RankCutoff

noncomputable section
namespace FCAppendix.Affine.Uniform06.RankUpperTail

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators

section IID
variable {Ω : Type*} [MeasurableSpace Ω]

omit [MeasurableSpace Ω] in
theorem count_add_compl {ι : Type*} [Fintype ι]
    (E : Set Ω) (s : Finset ι) (ω : ι → Ω) :
    PiBinomial.count E s ω+PiBinomial.count Eᶜ s ω=s.card := by
  classical
  rw [PiBinomial.count_eq_sum,PiBinomial.count_eq_sum,← Finset.sum_add_distrib]
  trans ∑ _j ∈ s, (1:ℕ)
  · apply Finset.sum_congr rfl
    intro j _hj
    by_cases hj : ω j ∈ E <;> simp [hj]
  · simp

theorem iid_count_upper_chernoff
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (E : Set Ω) (hE : MeasurableSet E) (N k : ℕ) (hkN : k ≤ N)
    {θ : ℝ} (hθ : 0 ≤ θ) :
    (Measure.pi fun _ : Fin N => μ).real
      {ω | k ≤ PiBinomial.count E Finset.univ ω} ≤
      Real.exp (-θ*k+N*Real.log (1-μ.real E+μ.real E*Real.exp θ)) := by
  classical
  let P := Measure.pi fun _ : Fin N => μ
  let w := μ.real E
  let Z := 1-w+w*Real.exp θ
  let f : (Fin N → Ω) → ℝ :=
    fun ω => Real.exp (-θ*PiBinomial.count Eᶜ Finset.univ ω)
  let A : Set (Fin N → Ω) := {ω | k ≤ PiBinomial.count E Finset.univ ω}
  have hA : MeasurableSet A :=
    (PiBinomial.measurable_count E hE Finset.univ) (measurableSet_Ici (a := k))
  have hf : Measurable f := by
    exact Real.measurable_exp.comp (measurable_const.mul
      ((measurable_of_countable (fun n : ℕ => (n : ℝ))).comp
        (PiBinomial.measurable_count Eᶜ hE.compl Finset.univ)))
  have hfbound (ω : Fin N → Ω) : |f ω| ≤ 1 := by
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hθ) (Nat.cast_nonneg _))
  have hfi : Integrable f P :=
    Integrable.of_bound hf.aestronglyMeasurable 1 (Filter.Eventually.of_forall hfbound)
  have hpoint (ω : Fin N → Ω) : A.indicator (fun _ => (1:ℝ)) ω ≤
      Real.exp (θ*(N-k:ℕ))*f ω := by
    by_cases hω : ω ∈ A
    · rw [Set.indicator_of_mem hω]
      have hc := count_add_compl E (Finset.univ : Finset (Fin N)) ω
      simp only [Finset.card_univ,Fintype.card_fin] at hc
      have hk : k ≤ PiBinomial.count E Finset.univ ω := hω
      have hcmp : PiBinomial.count Eᶜ Finset.univ ω ≤ N-k := by omega
      have hcmpR : (PiBinomial.count Eᶜ Finset.univ ω : ℝ) ≤ (N-k:ℕ) := by
        exact_mod_cast hcmp
      dsimp [f]
      rw [← Real.exp_add]
      apply Real.one_le_exp
      nlinarith [mul_le_mul_of_nonneg_left hcmpR hθ]
    · rw [Set.indicator_of_notMem hω]
      exact mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
  have hint := integral_mono ((integrable_const (1:ℝ)).indicator hA)
    (hfi.const_mul _) hpoint
  have hiOne : (∫ ω, A.indicator (fun _ => (1:ℝ)) ω ∂P) = P.real A := by
    convert! integral_indicator_one (μ := P) hA using 1
  rw [hiOne,integral_const_mul] at hint
  have hexact := PiBinomial.integral_tilt_count μ (∅:Set Ω) Eᶜ
    MeasurableSet.empty hE.compl (Set.empty_disjoint _) θ hθ
    (Finset.univ : Finset (Fin N)) 0
  have hcf : μ.real (Eᶜ)=1-w := probReal_compl_eq_one_sub hE
  have hset : (∅ : Set Ω)ᶜ \ Eᶜ = E := by ext x; simp
  have hfeq : (∫ ω, f ω ∂P) = (w+(1-w)*Real.exp (-θ))^N := by
    simpa only [P,f,PiBinomial.count,Finset.filter_false,Finset.card_empty,
      if_pos rfl,hset,hcf,
      Finset.card_univ,Fintype.card_fin,PiBinomial.tiltMass,Nat.choose_zero_right,
      Nat.cast_one,pow_zero,one_mul,Nat.sub_zero, Set.mem_empty_iff_false, w, if_true] using hexact
  rw [hfeq] at hint
  have hw : 0 ≤ w := measureReal_nonneg
  have hθexp : 1 ≤ Real.exp θ := Real.one_le_exp hθ
  have hZ : 0 < Z := by
    dsimp [Z]
    nlinarith [mul_le_mul_of_nonneg_left hθexp hw]
  have hbase : w+(1-w)*Real.exp (-θ)=Real.exp (-θ)*Z := by
    have he : Real.exp (-θ)*Real.exp θ=1 := by
      rw [← Real.exp_add,neg_add_cancel,Real.exp_zero]
    dsimp [Z]
    nlinarith
  have he : Real.exp (θ*(N-k:ℕ))*(w+(1-w)*Real.exp (-θ))^N =
      Real.exp (-θ*k+N*Real.log Z) := by
    rw [hbase,mul_pow,← Real.exp_nat_mul,
      show Z^N=(Real.exp (Real.log Z))^N by rw [Real.exp_log hZ],
      ← Real.exp_nat_mul,← Real.exp_add,← Real.exp_add,Nat.cast_sub hkN]
    congr 1
    ring
  rw [he] at hint
  exact hint

end IID

theorem source_tilt_log_bound {w : ℝ}
    (hw : 0 ≤ w) (hwHi : w ≤ (17/20000:ℝ)) :
    Real.log (1-w+w*Real.exp (1/10:ℝ)) ≤ (901/10000000:ℝ) := by
  have hexp0 : 0 ≤ Real.exp (1/10:ℝ)-1 := by
    have h := Real.one_le_exp (show (0:ℝ) ≤ 1/10 by norm_num)
    linarith
  have hexpHi : Real.exp (1/10:ℝ)-1 ≤ (53/500:ℝ) := by
    linarith [RankCutoff.exp_tenth_upper]
  have harg : 0 < 1-w+w*Real.exp (1/10:ℝ) := by
    nlinarith [mul_nonneg hw hexp0]
  have hlog := Real.log_le_sub_one_of_pos harg
  have hprod := mul_le_mul hwHi hexpHi hexp0 (by norm_num : (0:ℝ) ≤ 17/20000)
  nlinarith

theorem source_low_below_count_upper
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (E : Set Ω) (hE : MeasurableSet E)
    (hwHi : μ.real E ≤ (17/20000:ℝ))
    (m c : ℕ) (hc : 0 < c) (hcm : 2*c ≤ m)
    (hcap : (c:ℝ) ≤ (999/2000:ℝ)*m) :
    (Measure.pi fun _ : Fin (m-1) => μ).real
      {ω | m-2*c ≤ PiBinomial.count E Finset.univ ω} ≤
      Real.exp (-(9/1000000:ℝ)*m) := by
  have hkN : m-2*c ≤ m-1 := by omega
  have h := iid_count_upper_chernoff μ E hE (m-1) (m-2*c) hkN
    (show (0:ℝ) ≤ 1/10 by norm_num)
  have hlog := source_tilt_log_bound (show 0 ≤ μ.real E from measureReal_nonneg) hwHi
  have hcount : ((m-2*c:ℕ):ℝ) = (m:ℝ)-2*c := by
    rw [Nat.cast_sub hcm]
    push_cast
    ring
  have hNm : ((m-1:ℕ):ℝ) ≤ (m:ℝ) := by exact_mod_cast Nat.sub_le m 1
  have hK : (m:ℝ)/1000 ≤ (m-2*c:ℕ) := by rw [hcount]; nlinarith
  apply h.trans
  apply Real.exp_le_exp.mpr
  have hm := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg (m-1))
  have hNm' := mul_le_mul_of_nonneg_right hNm (by norm_num : (0:ℝ) ≤ 901/10000000)
  nlinarith [(Nat.cast_nonneg m : (0:ℝ) ≤ (m:ℝ))]

end FCAppendix.Affine.Uniform06.RankUpperTail
