import FCAppendix.Affine.Uniform06.PreciseRootGood
import FCAppendix.Affine.Uniform06.SamplingPopulation

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.LiteralRootGood

open MeasureTheory Set LowBody
open scoped BigOperators
open Uniform07 LiteralExperiment RawMixedSource RawTiltedSource RawMarkedLaplace
open RawPathAdapter PreciseRootGood RareEmpiricalReplacement SamplingPopulation
open FCAppendix.Affine.WeightedSampling FiniteSampledLaplace

def statistics (i : Row) (g : GuardData) (s U : ℝ) : Fin 5 → RowRival → ℝ :=
  Fin.cons (rawWeight (xi i) g) (TiltedGood.statistics s U)

lemma statistics_measurable (i : Row) (g : GuardData) (s U : ℝ) :
    ∀ k,Measurable (statistics i g s U k) := by
  intro k
  refine Fin.cases ?_ (fun j => ?_) k
  · exact measurable_rawWeight (xi i) g
  · exact TiltedGood.statistics_measurable s U j

lemma statistics_unit (i : Row) (g : GuardData) (s U : ℝ) :
    ∀ k r,statistics i g s U k r ∈ Icc (0:ℝ) 1 := by
  intro k
  refine Fin.cases ?_ (fun j => ?_) k
  · exact rawWeight_bounds (xi i) g
  · exact TiltedGood.statistics_unit s U j

def good (i : Row) (G : Measure (ℝ × ℝ)) (g : GuardData)
    (s U b θ : ℝ) (N : ℕ) (ε : ℝ) : Set (Fin N → RowRival) :=
  RivalGood.good (tiltedSource i G b θ) (statistics i g s U) N ε

theorem measurable_good (i : Row) (G : Measure (ℝ × ℝ)) (g : GuardData)
    (s U b θ : ℝ) (N : ℕ) (ε : ℝ) : MeasurableSet (good i G g s U b θ N ε) :=
  RivalGood.measurable_good _ _ (statistics_measurable i g s U) N ε

theorem good_complement (i : Row) (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    (g : GuardData) (s U : ℝ) {b : ℝ} (hb : 0< b) (θ : ℝ)
    (N : ℕ) (hN : 0< N) {ε : ℝ} (hε : 0≤ε) :
    (Measure.pi (fun _ : Fin N => tiltedSource i G b θ)).real
      (good i G g s U b θ N ε)ᶜ≤10*Real.exp (-(2*ε^2)*(N:ℝ)) := by
  letI := tiltedSource_probability i G hb θ
  have hh := RivalGood.good_complement_le (tiltedSource i G b θ)
    (statistics i g s U) (fun k => (statistics_measurable i g s U k).aemeasurable)
    (fun k => ae_of_all _ (statistics_unit i g s U k)) N hN hε
  convert! hh using 1
  norm_num [good]
  ring

variable {N : ℕ} [Nonempty (Fin N)]

omit [Nonempty (Fin N)] in
theorem good_count_projection (i : Row) (G : Measure (ℝ × ℝ)) (g : GuardData)
    (s U b θ ε : ℝ) (ω : Fin N → RowRival)
    (hg : ω ∈ good i G g s U b θ N ε) :
    ω ∈ RivalGood.good (TiltedGood.law i G b θ) (TiltedGood.statistics s U) N ε := by
  intro k
  simpa only [good,statistics,RivalGood.empirical,Fin.cons_succ,
    TiltedGood.law,tiltedSource] using hg k.succ

omit [Nonempty (Fin N)] in
theorem original_good_path_conditions (i : Row)
    (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G] (g : GuardData)
    {b θ s U lo ε q z : ℝ} (hb : 0< b) (hbs : b< s) (hU : 0< U)
    (hlo : 0< lo) (hloU : U/2≤ lo) (hN : 0< N) {c : ℕ}
    (hfloor : |(c:ℝ)-(N:ℝ)*rho|≤1)
    (hpos : ε*(N:ℝ)+2<(N:ℝ)*(rho-TiltedGood.upperProbability i G b θ))
    (hroom : 2*ε*(N:ℝ)+3≤(N:ℝ)*(TiltedGood.lowerProbability i G b θ-
      (rho-TiltedGood.upperProbability i G b θ)))
    (hq : 0< q) (hεq : 12*ε≤ q)
    (hstrip : q≤(TiltedGood.law i G b θ).real (CostAmplification.activeStrip s U))
    (hz : 0< z) (hεz : 8*ε≤ z)
    (hwmean : z/2≤ weightMean i G b θ g)
    (ω : Fin N → RowRival) (hno : ∀ j,(ω j).1≠1)
    (hg : ω ∈ good i G g s U b θ N ε) :
    ValidCounts c ω ∧
      ((imbalanceSum ω).natAbs:ℝ)<
        totalWeight (rowWeights (rawWeight (xi i) g) (rawWeight_bounds (xi i) g) ω) ∧
      q/(4*U)+((imbalanceSum ω).natAbs:ℝ)/(lo*(N:ℝ))≤
        empirical (FullReciprocalMean.reciprocal b) N ω := by
  have hc := source_good_counts_and_reciprocal i G hb hbs hU hlo hloU hN hfloor
    hpos hroom hq hεq hstrip ω hno (good_count_projection i G g s U b θ ε ω hg)
  have hw := hg 0
  change |empirical (rawWeight (xi i) g) N ω-weightMean i G b θ g|<ε at hw
  have hNr : 0<(N:ℝ) := Nat.cast_pos.mpr hN
  have htw : empirical (rawWeight (xi i) g) N ω=
      totalWeight (rowWeights (rawWeight (xi i) g) (rawWeight_bounds (xi i) g) ω)/(N:ℝ) := rfl
  rw [htw] at hw
  have hs : 2*ε< totalWeight
      (rowWeights (rawWeight (xi i) g) (rawWeight_bounds (xi i) g) ω)/(N:ℝ) := by
    linarith [(abs_lt.mp hw).1]
  have hW := (lt_div_iff₀ hNr).mp hs
  exact ⟨hc.1,hc.2.1.trans_lt hW,hc.2.2⟩

end FCAppendix.Affine.Uniform06.LiteralRootGood
