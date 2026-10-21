import FCAppendix.AppendixRepair.GeneralLow.Primitive
import FCAppendix.AppendixRepair.LowCounts

set_option maxHeartbeats 2000000
noncomputable section
namespace FCAppendix.Appendix08.GeneralLow
open MeasureTheory ProbabilityTheory Set Filter Topology Game Bayes
open Affine Affine.LowBody Affine.Hybrid Existence.Distributional
open Affine.AppendixRepair.TriangularLow

instance lowBroadcast_map_probability {d : ℝ} (nu : Measure (LowValue d))
    [IsProbabilityMeasure nu] : IsProbabilityMeasure (nu.map lowBroadcast) :=
  Measure.isProbabilityMeasure_map (measurable_lowBroadcast d).aemeasurable

def chosenLowKernel {d : ℝ} (mu : Measure (LowValue d)) [IsProbabilityMeasure mu]
    (pi : Law (A := LowValue d) mu) : Kernel (LowValue d) (LowValue d) := by
  letI : Nonempty (LowValue d) := nonempty_of_isProbabilityMeasure mu
  exact (pi.1 : Measure (LowValue d × LowValue d)).condKernel

instance chosenLowKernel_markov {d : ℝ} (mu : Measure (LowValue d))
    [IsProbabilityMeasure mu] (pi : Law (A := LowValue d) mu) :
    IsMarkovKernel (chosenLowKernel mu pi) := by
  letI : Nonempty (LowValue d) := nonempty_of_isProbabilityMeasure mu
  exact inferInstanceAs
    (IsMarkovKernel (pi.1 : Measure (LowValue d × LowValue d)).condKernel)

theorem chosenLowKernel_joint {d : ℝ} (mu : Measure (LowValue d))
    [IsProbabilityMeasure mu] (pi : Law (A := LowValue d) mu) :
    mu ⊗ₘ chosenLowKernel mu pi = (pi.1 : Measure (LowValue d × LowValue d)) := by
  letI : Nonempty (LowValue d) := nonempty_of_isProbabilityMeasure mu
  have hmarg : (pi.1 : Measure (LowValue d × LowValue d)).fst = mu := pi.2
  calc
    mu ⊗ₘ chosenLowKernel mu pi =
        (pi.1 : Measure (LowValue d × LowValue d)).fst ⊗ₘ chosenLowKernel mu pi :=
      congrArg (fun nu : Measure (LowValue d) => nu ⊗ₘ chosenLowKernel mu pi) hmarg.symm
    _ = _ := by
      change (pi.1 : Measure (LowValue d × LowValue d)).fst ⊗ₘ
        (pi.1 : Measure (LowValue d × LowValue d)).condKernel = _
      exact Measure.disintegrate _ _

section Rows
variable (C : CategoryRows) (d η : ℝ) (hη0 : 0 ≤ η) (hη1 : η < 1)
  (c : ℕ → ℕ) (start : ℕ)
  (mu : Measure (LowValue d)) [IsProbabilityMeasure mu]
  (pi : ℕ → Law (A := LowValue d) mu)
  (B : ℕ → BidClasses d) (H : ∀ n, HigherLaws (B n))
  (hA : ∀ n, ∀ b ∈ (B n).activeSet, d < ((1 + η) / 2) * b)
  (hP : ∀ n, ∀ b ∈ (B n).privateSet, d < b)
  (HC : ∀ n, Market.SourceHC (n + start + 1) (c (n + start + 1)) (B n) (H n)
    hη0 hη1 (hA n) (hP n)
    (C.s (n + start + 1)) (C.a (n + start + 1)) (C.h (n + start + 1))
    (C.s_nonneg (n + start + 1)) (C.a_nonneg (n + start + 1))
    (C.h_nonneg (n + start + 1)) (C.total (n + start + 1)) mu (pi n))

def rowMarket (n : ℕ) : FiniteGame (n + start + 1) 2 (c (n + start + 1)) unitInterval :=
  Market.game (n + start + 1) (c (n + start + 1)) (B n) (H n)
    hη0 hη1 (hA n) (hP n)
    (C.s (n + start + 1)) (C.a (n + start + 1)) (C.h (n + start + 1))
    (C.s_nonneg (n + start + 1)) (C.a_nonneg (n + start + 1))
    (C.h_nonneg (n + start + 1)) (C.total (n + start + 1)) mu (pi n) (HC n)

theorem triangular_uniform_counts (hd : 0 ≤ d)
    {a h : ℝ} (ha : Tendsto C.a atTop (𝓝 a)) (hh : Tendsto C.h atTop (𝓝 h))
    (Gref : Measure ℝ) [IsProbabilityMeasure Gref] (ρ : ℝ)
    (hc : Tendsto (fun m => (c m : ℝ) / (m : ℝ)) atTop (𝓝 ρ))
    (hrank : ρ < a + h / 2) :
    ∀ epsilon > 0, ∀ᶠ n in atTop,
      ∀ i : Fin (n + start + 1), ∀ act : JointAction 2, act.bid ≤ d →
      ((problem (rowMarket C d η hη0 hη1 c start mu pi B H hA hP HC n) i).outcome act).success <
        epsilon := by
  have ht := (higherUnderflow_tendsto_zero C ha hh Gref c ρ hc hrank).comp
    (tendsto_add_atTop_nat (start + 1))
  have ht' : Tendsto (fun n => (CommonList.iid (C.law Gref (n + start + 1))
      (n + start)).prob (HigherUnderflow (c (n + start + 1)))) atTop (𝓝 0) := by
    convert! ht using 1
  intro epsilon hepsilon
  filter_upwards [ht'.eventually_lt_const hepsilon] with n hn
  intro i act hbd
  have hb := DirectBounds.source_counts_bound (B n) hd (H n) hη0 hη1 (hA n) (hP n)
    (C.s (n + start + 1)) (C.a (n + start + 1)) (C.h (n + start + 1))
    (C.s_nonneg (n + start + 1)) (C.a_nonneg (n + start + 1))
    (C.h_nonneg (n + start + 1)) (C.total (n + start + 1)) Gref mu (pi n)
    (Market.selector (n + start + 1) (c (n + start + 1)) (B n) (H n)
      hη0 hη1 (hA n) (hP n)
      (C.s (n + start + 1)) (C.a (n + start + 1)) (C.h (n + start + 1))
      (C.s_nonneg (n + start + 1)) (C.a_nonneg (n + start + 1))
      (C.h_nonneg (n + start + 1)) (C.total (n + start + 1)) mu (pi n) (HC n)) i act hbd
  exact hb.1.trans_lt hn

theorem triangular_every_fixed_low_kernel (hd : 0 ≤ d)
    {a h : ℝ} (ha : Tendsto C.a atTop (𝓝 a)) (hh : Tendsto C.h atTop (𝓝 h))
    (Gref : Measure ℝ) [IsProbabilityMeasure Gref] (ρ : ℝ)
    (hc : Tendsto (fun m => (c m : ℝ) / (m : ℝ)) atTop (𝓝 ρ))
    (hrank : ρ < a + h / 2)
    (sigmaLow : ℕ → Kernel (LowValue d) (LowValue d))
    [∀ n, IsMarkovKernel (sigmaLow n)] :
    ∀ w : LowValue d, ∀ i : (n : ℕ) → Fin (n + start + 1), ∀ f : Fin 3 → ℝ,
      Tendsto (fun n => (mixedCountLaw
        (rowMarket C d η hη0 hη1 c start mu pi B H hA hP HC n) (i n)
          ((sigmaLow n w).map lowBroadcast)).expect f) atTop (𝓝 (f 0)) := by
  intro w i f
  let nu : ℕ → Measure (JointAction 2) := fun n => (sigmaLow n w).map lowBroadcast
  haveI : ∀ n, IsProbabilityMeasure (nu n) := fun n =>
    Measure.isProbabilityMeasure_map (measurable_lowBroadcast d).aemeasurable
  apply LowCounts.mixed_low_test_tendsto (fun n => n + start + 1)
    (fun n => c (n + start + 1))
    (rowMarket C d η hη0 hη1 c start mu pi B H hA hP HC) i nu d
    (Eventually.of_forall fun n => LowCounts.lowBroadcast_map_support (sigmaLow n w))
    (triangular_uniform_counts C d η hη0 hη1 c start mu pi B H hA hP HC
      hd ha hh Gref ρ hc hrank) f

theorem triangular_chosen_low_kernel (hd : 0 ≤ d)
    {a h : ℝ} (ha : Tendsto C.a atTop (𝓝 a)) (hh : Tendsto C.h atTop (𝓝 h))
    (Gref : Measure ℝ) [IsProbabilityMeasure Gref] (ρ : ℝ)
    (hc : Tendsto (fun m => (c m : ℝ) / (m : ℝ)) atTop (𝓝 ρ))
    (hrank : ρ < a + h / 2) :
    ∀ w : LowValue d, ∀ i : (n : ℕ) → Fin (n + start + 1), ∀ f : Fin 3 → ℝ,
      Tendsto (fun n => (mixedCountLaw
        (rowMarket C d η hη0 hη1 c start mu pi B H hA hP HC n) (i n)
          ((chosenLowKernel mu (pi n) w).map lowBroadcast)).expect f)
        atTop (𝓝 (f 0)) :=
  triangular_every_fixed_low_kernel C d η hη0 hη1 c start mu pi B H hA hP HC
    hd ha hh Gref ρ hc hrank (fun n => chosenLowKernel mu (pi n))

theorem triangular_every_fixed_action_kernel (hd : 0 ≤ d)
    {a h : ℝ} (ha : Tendsto C.a atTop (𝓝 a)) (hh : Tendsto C.h atTop (𝓝 h))
    (Gref : Measure ℝ) [IsProbabilityMeasure Gref] (ρ : ℝ)
    (hc : Tendsto (fun m => (c m : ℝ) / (m : ℝ)) atTop (𝓝 ρ))
    (hrank : ρ < a + h / 2)
    (sigmaLow : ℕ → Kernel (LowValue d) (JointAction 2))
    [∀ n, IsMarkovKernel (sigmaLow n)] :
    ∀ w : LowValue d,
      (∀ᶠ n in atTop, ∀ᵐ act ∂sigmaLow n w, act.bid ≤ d) →
      ∀ i : (n : ℕ) → Fin (n + start + 1), ∀ f : Fin 3 → ℝ,
        Tendsto (fun n => (mixedCountLaw
          (rowMarket C d η hη0 hη1 c start mu pi B H hA hP HC n) (i n)
            (sigmaLow n w)).expect f) atTop (𝓝 (f 0)) := by
  intro w hsupport i f
  exact LowCounts.mixed_low_test_tendsto (fun n => n + start + 1)
    (fun n => c (n + start + 1))
    (rowMarket C d η hη0 hη1 c start mu pi B H hA hP HC) i
    (fun n => sigmaLow n w) d hsupport
    (triangular_uniform_counts C d η hη0 hη1 c start mu pi B H hA hP HC
      hd ha hh Gref ρ hc hrank) f

theorem triangular_actual_conditional_counts (hd : 0 ≤ d)
    {a h : ℝ} (ha : Tendsto C.a atTop (𝓝 a)) (hh : Tendsto C.h atTop (𝓝 h))
    (Gref : Measure ℝ) [IsProbabilityMeasure Gref] (ρ : ℝ)
    (hc : Tendsto (fun m => (c m : ℝ) / (m : ℝ)) atTop (𝓝 ρ))
    (hrank : ρ < a + h / 2) (v : ℝ)
    (hsupport : ∀ᶠ n in atTop, ∀ᵐ act ∂
      (rowMarket C d η hη0 hη1 c start mu pi B H hA hP HC n).σ v, act.bid ≤ d)
    (f : Fin 3 → ℝ) :
    Tendsto (fun n => (conditionalTypeCountLaw
      (rowMarket C d η hη0 hη1 c start mu pi B H hA hP HC n)
        (Nat.succ_pos (n + start)) v).expect f) atTop (𝓝 (f 0)) := by
  exact LowCounts.conditional_low_test_tendsto (fun n => n + start + 1)
    (fun n => c (n + start + 1))
    (rowMarket C d η hη0 hη1 c start mu pi B H hA hP HC)
    (fun n => Nat.succ_pos (n + start)) v d hsupport
    (triangular_uniform_counts C d η hη0 hη1 c start mu pi B H hA hP HC
      hd ha hh Gref ρ hc hrank) f

end Rows
end FCAppendix.Appendix08.GeneralLow
