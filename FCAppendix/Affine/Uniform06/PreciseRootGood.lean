import FCAppendix.Affine.Uniform06.RawPathGlobalResponse
import FCAppendix.Affine.Uniform06.SourceCoarseIntegral
import FCAppendix.Affine.Uniform06.EarlyCoarseMargins

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.PreciseRootGood

open MeasureTheory ProbabilityTheory Set LowBody
open scoped BigOperators
open Uniform07 LiteralExperiment RawMixedSource RawTiltedSource RawGoodGeometry
open RawPathAdapter RawPathRootReplacement RareEmpiricalReplacement ReciprocalSecantBounds
open FCAppendix.Affine.ClippedResidual FCAppendix.Affine.WeightedSampling

variable {N : ℕ} [Nonempty (Fin N)]

omit [Nonempty (Fin N)] in
theorem source_valid_counts (i : Row)
    (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    {b θ s U ε : ℝ} (hb : 0< b) (hN : 0< N) {c : ℕ}
    (hfloor : |(c:ℝ)-(N:ℝ)*rho|≤1)
    (hpos : ε*(N:ℝ)+2<(N:ℝ)*(rho-TiltedGood.upperProbability i G b θ))
    (hroom : 2*ε*(N:ℝ)+3≤(N:ℝ)*(TiltedGood.lowerProbability i G b θ-
      (rho-TiltedGood.upperProbability i G b θ)))
    (ω : Fin N → RowRival) (hno : ∀ j,(ω j).1≠1)
    (hg : ω ∈ RivalGood.good (TiltedGood.law i G b θ) (TiltedGood.statistics s U) N ε) :
    ValidCounts c ω := by
  have hc1 : classCount 1 ω=0 := by simp [classCount,hno]
  have herr := source_count_errors i G hb θ s U hN ω hg
  have hcL := (abs_le.mp hfloor).1
  have hcU := (abs_le.mp hfloor).2
  have hu2 : classCount 2 ω≤ c := by
    exact_mod_cast (show (classCount 2 ω:ℝ)≤(c:ℝ) by
      linarith [(abs_lt.mp herr.2.1).2])
  have hu3 : classCount 3 ω≤ c := by
    exact_mod_cast (show (classCount 3 ω:ℝ)≤(c:ℝ) by
      linarith [(abs_lt.mp herr.2.2.1).2])
  have hl2 : c-classCount 2 ω≤1+classCount 0 ω := by
    have hh : ((c-classCount 2 ω:ℕ):ℝ)≤((1+classCount 0 ω:ℕ):ℝ) := by
      rw [Nat.cast_sub hu2,Nat.cast_add,Nat.cast_one]
      linarith [(abs_lt.mp herr.1).1,(abs_lt.mp herr.2.1).1]
    exact_mod_cast hh
  have hl3 : c-classCount 3 ω≤1+classCount 0 ω := by
    have hh : ((c-classCount 3 ω:ℕ):ℝ)≤((1+classCount 0 ω:ℕ):ℝ) := by
      rw [Nat.cast_sub hu3,Nat.cast_add,Nat.cast_one]
      linarith [(abs_lt.mp herr.1).1,(abs_lt.mp herr.2.2.1).1]
    exact_mod_cast hh
  constructor
  · simpa only [hc1,zero_add] using hu2
  · simpa only [hc1,zero_add] using hu3
  · simpa only [hc1,Nat.sub_zero] using hl2
  · simpa only [hc1,Nat.sub_zero] using hl3

omit [Nonempty (Fin N)] in
lemma empirical_reciprocal_above_strip {b s U : ℝ} (hb : 0< b) (hbs : b< s)
    (_hU : 0< U) (_hN : 0< N) (ω : Fin N → RowRival) :
    (∑ j,TiltedGood.stripTest s U (ω j))/((N:ℝ)*U)≤
      empirical (FullReciprocalMean.reciprocal b) N ω := by
  have hpoint (r : RowRival) : TiltedGood.stripTest s U r/U≤ FullReciprocalMean.reciprocal b r := by
    by_cases hs : r ∈ CostAmplification.activeStrip s U
    · have hbr : b< r.2 := hbs.trans hs.2.1
      simp only [TiltedGood.stripTest,indicator_of_mem hs,one_div,
        FullReciprocalMean.reciprocal,FullReciprocalMean.lowerTest,if_pos hs.1,
        reciprocalTerm,if_pos hbr]
      simpa only [one_div] using one_div_le_one_div_of_le (hb.trans hbr) hs.2.2
    · rw [TiltedGood.stripTest,indicator_of_notMem hs,zero_div]
      exact (FullReciprocalMean.reciprocal_bounds hb le_rfl r).1
  have hh := div_le_div_of_nonneg_right (Finset.sum_le_sum (s := Finset.univ) (fun j _ => hpoint (ω j)))
    (Nat.cast_nonneg N)
  simp only [← Finset.sum_div] at hh
  unfold empirical
  convert! hh using 1
  ring

omit [Nonempty (Fin N)] in

theorem source_good_counts_and_reciprocal (i : Row)
    (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    {b θ s U lo ε q : ℝ} (hb : 0< b) (hbs : b< s) (hU : 0< U)
    (hlo : 0< lo) (hloU : U/2≤ lo) (hN : 0< N) {c : ℕ}
    (hfloor : |(c:ℝ)-(N:ℝ)*rho|≤1)
    (hpos : ε*(N:ℝ)+2<(N:ℝ)*(rho-TiltedGood.upperProbability i G b θ))
    (hroom : 2*ε*(N:ℝ)+3≤(N:ℝ)*(TiltedGood.lowerProbability i G b θ-
      (rho-TiltedGood.upperProbability i G b θ)))
    (hq : 0< q) (hεq : 12*ε≤ q)
    (hstrip : q≤(TiltedGood.law i G b θ).real (CostAmplification.activeStrip s U))
    (ω : Fin N → RowRival) (hno : ∀ j,(ω j).1≠1)
    (hg : ω ∈ RivalGood.good (TiltedGood.law i G b θ) (TiltedGood.statistics s U) N ε) :
    ValidCounts c ω ∧
      ((imbalanceSum ω).natAbs:ℝ)≤2*ε*(N:ℝ) ∧
      q/(4*U)+((imbalanceSum ω).natAbs:ℝ)/(lo*(N:ℝ))≤
        empirical (FullReciprocalMean.reciprocal b) N ω := by
  have hNr : 0<(N:ℝ) := Nat.cast_pos.mpr hN
  have hc1 : classCount 1 ω=0 := by simp [classCount,hno]
  have herr := source_count_errors i G hb θ s U hN ω hg
  have hcL := (abs_le.mp hfloor).1
  have hcU := (abs_le.mp hfloor).2
  have hu2 : classCount 2 ω≤ c := by
    exact_mod_cast (show (classCount 2 ω:ℝ)≤(c:ℝ) by
      linarith [(abs_lt.mp herr.2.1).2])
  have hu3 : classCount 3 ω≤ c := by
    exact_mod_cast (show (classCount 3 ω:ℝ)≤(c:ℝ) by
      linarith [(abs_lt.mp herr.2.2.1).2])
  have hl2 : c-classCount 2 ω≤1+classCount 0 ω := by
    apply (Nat.cast_le (α:=ℝ)).mp
    rw [Nat.cast_sub hu2,Nat.cast_add,Nat.cast_one]
    linarith [(abs_lt.mp herr.1).1,(abs_lt.mp herr.2.1).1]
  have hl3 : c-classCount 3 ω≤1+classCount 0 ω := by
    apply (Nat.cast_le (α:=ℝ)).mp
    rw [Nat.cast_sub hu3,Nat.cast_add,Nat.cast_one]
    linarith [(abs_lt.mp herr.1).1,(abs_lt.mp herr.2.2.1).1]
  have hvalid : ValidCounts c ω := by
    constructor
    · simpa only [hc1,zero_add] using hu2
    · simpa only [hc1,zero_add] using hu3
    · simpa only [hc1,Nat.sub_zero] using hl2
    · simpa only [hc1,Nat.sub_zero] using hl3
  have hk : ((imbalanceSum ω).natAbs:ℝ)≤2*ε*(N:ℝ) := by
    rw [← draws_eq_natAbs,draws_eq_abs,RawMixedSource.sign_count]
    have hh := abs_sub
      ((classCount 2 ω:ℝ)-(N:ℝ)*TiltedGood.upperProbability i G b θ)
      ((classCount 3 ω:ℝ)-(N:ℝ)*TiltedGood.upperProbability i G b θ)
    have he : (classCount 2 ω:ℝ)-classCount 3 ω=
        ((classCount 2 ω:ℝ)-(N:ℝ)*TiltedGood.upperProbability i G b θ)-
        ((classCount 3 ω:ℝ)-(N:ℝ)*TiltedGood.upperProbability i G b θ) := by ring
    rw [he]
    linarith [herr.2.1,herr.2.2.1]
  have hs : (q-ε)*(N:ℝ)≤∑ j,TiltedGood.stripTest s U (ω j) := by
    have hh := mul_le_mul_of_nonneg_left hstrip hNr.le
    rw [stripSet_card] at herr
    linarith [(abs_lt.mp herr.2.2.2).1]
  have hbase := (div_le_div_of_nonneg_right hs (mul_pos hNr hU).le).trans
    (empirical_reciprocal_above_strip hb hbs hU hN ω)
  have hε : 0≤ε := by
    have hh := abs_nonneg ((classCount 2 ω:ℝ)-(N:ℝ)*TiltedGood.upperProbability i G b θ)
    have hh' : 0<ε*(N:ℝ) := hh.trans_lt herr.2.1
    exact (pos_of_mul_pos_left hh' hNr.le).le
  have hdel : ((imbalanceSum ω).natAbs:ℝ)/(lo*(N:ℝ))≤4*ε/U := by
    have hh := div_le_div_of_nonneg_right hk (mul_pos hlo hNr).le
    have he : 2*ε*(N:ℝ)/(lo*(N:ℝ))=2*ε/lo := by field_simp [hNr.ne']
    rw [he] at hh
    refine hh.trans ?_
    apply (div_le_div_iff₀ hlo hU).mpr
    nlinarith [mul_le_mul_of_nonneg_left hloU (show 0≤4*ε by positivity)]
  refine ⟨hvalid,hk,?_⟩
  have he : (q-ε)*(N:ℝ)/((N:ℝ)*U)=(q-ε)/U := by field_simp [hNr.ne']
  rw [he] at hbase
  have hh : q/(4*U)+4*ε/U≤(q-ε)/U := by
    apply (le_div_iff₀ hU).mpr
    field_simp [hU.ne']
    linarith
  exact (add_le_add le_rfl hdel).trans (hh.trans hbase)

end FCAppendix.Affine.Uniform06.PreciseRootGood
