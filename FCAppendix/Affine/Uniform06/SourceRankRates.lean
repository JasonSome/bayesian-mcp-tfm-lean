import FCAppendix.Affine.Uniform06.PureRankProbability
import FCAppendix.Affine.Uniform06.SourcePureDuplicate

noncomputable section
namespace FCAppendix.Affine.Uniform06.SourceRankRates

open MeasureTheory Set Filter Topology
open FCAppendix.Affine.Uniform07 LowBody
open PureRankCounts PureRankProbability PureDuplicateIntervals
open EqualCanonicalRegularity PureDuplicateRare

def Lm (i : Row) (m : ℕ) : ℝ :=
  Bayes.binomBelow (m-1) ((1+cutoff i)/2) (capacity m)

theorem source_rank_parameter (i : Row) : ((1+cutoff i)/2) ∈ Ioo (0:ℝ) 1 := by
  have ht := cutoff_pos i
  have ht1 := cutoff_lt_one i
  constructor <;> linarith

theorem source_rank_KL (i : Row) :
    Ample.binaryKL rho ((1+cutoff i)/2)=LowChernoff.rankI0 i := rfl

theorem source_rank_nonnegative (i : Row) : 0 ≤ LowChernoff.rankI0 i := by
  rw [← source_rank_KL]
  exact LowBody.binaryKL_nonneg (source_rank_parameter i).1 (source_rank_parameter i).2
    (by norm_num [rho]) (by norm_num [rho])

theorem eventually_Lm_lower (i : Row) :
    ∀ᶠ m : ℕ in atTop, Real.exp (-(m:ℝ)*(3/1000000:ℝ)) ≤ Lm i m := by
  have hh := UnilateralRank.eventually_rankLower_ge_exp capacity ((1+cutoff i)/2) rho
    (source_rank_parameter i) (by norm_num [rho,mem_Ioo])
    PhysicalRates.capacity_density_tendsto
    (by rw [source_rank_KL]; exact RankCutoff.rankI0_lt_three_micro i)
  exact hh

theorem source_capacity_twice (m : ℕ) : 2*capacity m ≤ m := by
  have hc := (PhysicalRates.capacity_floor_bounds m).2
  have hreal : (2*capacity m:ℝ) ≤ m := by
    norm_num only [rho] at hc
    nlinarith [show (0:ℝ) ≤ m from Nat.cast_nonneg m]
  exact_mod_cast hreal

theorem source_conditional_tilt (i : Row) :
    ∃ θ γ : ℝ, 0 < θ ∧ 0 < γ ∧
      γ=(1-rho)*((1-cutoff i)/2)/((1-cutoff i)/2+RankCutoff.Mstar i)*
        (1-Real.exp (-θ))-rho*θ := by
  have hh := source_conditional_mean_gap (cutoff_lt_one i)
    (show 0 < delta by norm_num [delta]) (show delta < 1 by norm_num [delta])
    (RankCutoff.Mstar_bounds i).1.le
    (lt_of_lt_of_le (RankCutoff.Mstar_below_source_guards i)
      (min_le_right _ _))
  have hρ : 0 < rho := by norm_num [rho]
  have hgap : rho < (1-rho)*((1-cutoff i)/2)/
      ((1-cutoff i)/2+RankCutoff.Mstar i) := by
    convert! hh using 1 <;> norm_num [rho,delta]
  exact exists_positive_tilt hρ hgap

theorem eventually_source_pure_relative (i : Row) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ᶠ m : ℕ in atTop,
      ∀ (G : Measure ℝ) (_hG : IsProbabilityMeasure G) (b : ℝ),
        0 < b → G {b}=0 → sourceRank (cutoff i) G b ≤ RankCutoff.Mstar i →
        |qPure (m-1) (capacity m) (kappa i) (cutoff i) G b /
          Rank.pureRank (m-1) (capacity m) ((1+cutoff i)/2)
            (sourceRank (cutoff i) G b)-1| ≤
          Real.exp (-γ*m)+Real.exp (-(6/1000000:ℝ)*m) := by
  obtain ⟨θ,γ,hθ,hγ,hdef⟩ := source_conditional_tilt i
  refine ⟨γ,hγ,?_⟩
  filter_upwards [eventually_Lm_lower i,eventually_ge_atTop (4:ℕ)] with m hL hm
  intro G hG b hb hatom hM
  letI := hG
  have hc := PhysicalRates.capacity_positive (show 3 ≤ m by omega)
  have hcm := source_capacity_twice m
  have hcond := source_relative_exponent hc (show capacity m ≤ m by omega)
    (cutoff_lt_one i) (show 0 ≤ rho by norm_num [rho])
    (show rho ≤ 1 by norm_num [rho])
    (show 0 ≤ sourceRank (cutoff i) G b from mul_nonneg (cutoff_pos i).le measureReal_nonneg)
    hM hθ.le (PhysicalRates.capacity_floor_bounds m).2 hdef
  have hh := qPure_relative_finite (cutoff_pos i).le (cutoff_lt_one i)
    (show kappa i ≤ 1 by cases i <;> norm_num [kappa,kappaQ,xiQ,etaQ]) hb G hatom
    m (capacity m) (by omega) hc hcm (PhysicalRates.capacity_floor_bounds m).2
    (hM.trans (RankCutoff.Mstar_bounds i).2.le) hθ.le hcond hL
  convert! hh using 1
  ring

theorem eventually_source_pure_duplicate_relative (i : Row) :
    ∀ᶠ m : ℕ in atTop, 0 < Lm i m ∧
      ∀ (G : Measure (ℝ × ℝ)) (_hG : IsProbabilityMeasure G),
        G.map Prod.fst=LowChernoff.conditionalValueLaw i →
        (∀ᵐ p ∂G, LowChernoff.physicalFloor i p.1 ≤ p.2) →
        ∀ b : ℝ, 0 < b → b ≤ RankCutoff.Mstar i →
          expectedPureDuplicate (N := m-1) (cutoff i) 0 (1-cutoff i) (kappa i)
            (G.map Prod.snd) (capacity m) b/Lm i m ≤
              Real.exp (-(6/1000000:ℝ)*m) := by
  filter_upwards [eventually_Lm_lower i,eventually_ge_atTop (4:ℕ)] with m hL hm
  have hL0 := (Real.exp_pos _).trans_le hL
  refine ⟨hL0,?_⟩
  intro G hG hv hf b hb hbM
  letI := hG
  have hu := source_pure_duplicate_exponential i G hv hf hm b hb hbM
  apply (div_le_iff₀ hL0).mpr
  have hh := mul_le_mul_of_nonneg_left hL (Real.exp_pos (-(6/1000000:ℝ)*m)).le
  have he : Real.exp (-(6/1000000:ℝ)*m)*Real.exp (-(m:ℝ)*(3/1000000:ℝ))=
      Real.exp (-(9/1000000:ℝ)*m) := by rw [← Real.exp_add]; congr 1; ring
  rw [he] at hh
  exact hu.trans hh

def equalRateConstant (i : Row) : ℝ :=
  (LowChernoff.thetaQ i:ℝ)*rho+LowChernoff.rankI0 i+LowChernoff.sourceGap i

def equalRelativeGap (i : Row) : ℝ := LowChernoff.sourceGap i-3/1000000

theorem equalRelativeGap_pos (i : Row) : 0 < equalRelativeGap i := by
  cases i <;> norm_num [equalRelativeGap,LowChernoff.sourceGap]

theorem source_equal_exponent_upper (i : Row) {m : ℕ} (hm : 1 ≤ m) :
    (LowChernoff.thetaQ i:ℝ)*(capacity m:ℝ)-
      (m-1:ℕ)*equalRateConstant i ≤
        equalRateConstant i-(m:ℝ)*LowChernoff.sourceGap i := by
  have hθ : 0 ≤ (LowChernoff.thetaQ i:ℝ) := by cases i <;> norm_num [LowChernoff.thetaQ]
  have hc := mul_le_mul_of_nonneg_left (PhysicalRates.capacity_floor_bounds m).2 hθ
  have hmcast : ((m-1:ℕ):ℝ)=(m:ℝ)-1 := by rw [Nat.cast_sub hm]; norm_num
  rw [hmcast]
  unfold equalRateConstant at *
  have hI := mul_nonneg (Nat.cast_nonneg m) (source_rank_nonnegative i)
  nlinarith

theorem eventually_source_equal_duplicate_relative (i : Row) :
    ∀ᶠ m : ℕ in atTop, 0 < Lm i m ∧
      ∀ (G : Measure (ℝ × ℝ)) (_hG : IsProbabilityMeasure G),
        G.map Prod.fst=LowChernoff.conditionalValueLaw i →
        (∀ᵐ p ∂G, LowChernoff.physicalFloor i p.1 ≤ p.2) →
        ∀ b : ℝ, 0 < b → b ≤ (501/1000:ℝ)*cutoff i →
          expectedEqualDuplicate
            (Measure.pi fun _ : Fin (m-1) => sourceRivalLaw (cutoff i) (G.map Prod.snd))
            (xi i) (capacity m) b/Lm i m ≤
              Real.exp (equalRateConstant i-(m:ℝ)*equalRelativeGap i) := by
  filter_upwards [eventually_Lm_lower i,eventually_ge_atTop (2:ℕ)] with m hL hm
  have hL0 := (Real.exp_pos _).trans_le hL
  refine ⟨hL0,?_⟩
  intro G hG hv hf b hb hbz
  letI := hG
  have hu := (source_equal_duplicate_level_and_increment i G hv hf hm).1 b hb hbz
  have hexp := Real.exp_le_exp.mpr (source_equal_exponent_upper i (by omega : 1 ≤ m))
  apply (div_le_iff₀ hL0).mpr
  have hh := mul_le_mul_of_nonneg_left hL
    (Real.exp_pos (equalRateConstant i-(m:ℝ)*equalRelativeGap i)).le
  have he : Real.exp (equalRateConstant i-(m:ℝ)*equalRelativeGap i)*
      Real.exp (-(m:ℝ)*(3/1000000:ℝ))=
        Real.exp (equalRateConstant i-(m:ℝ)*LowChernoff.sourceGap i) := by
    rw [← Real.exp_add]
    congr 1
    unfold equalRelativeGap
    ring
  rw [he] at hh
  exact (hu.trans hexp).trans hh

end FCAppendix.Affine.Uniform06.SourceRankRates
