import FCAppendix.AppendixRepair.GeneralLow.CountEndpoint
import FCAppendix.AppendixRepair.GeneralLow.C0Floor

noncomputable section
namespace FCAppendix.Appendix08.GeneralLow
open MeasureTheory ProbabilityTheory Set Filter Topology Game Bayes
open Affine Affine.LowBody Affine.Hybrid Existence.Distributional
open Affine.AppendixRepair.TriangularLow

def ChosenCategoricalRows (C : CategoryRows) (d η : ℝ) (hd : 0 ≤ d)
    (hη0 : 0 ≤ η) (hη1 : η < 1) (c : ℕ → ℕ)
    (Gref : Measure ℝ) [IsProbabilityMeasure Gref]
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu]
    (pi : ℕ → Law (A := LowValue d) mu) : Prop :=
  ∀ᶠ m in atTop,
    ∃ L : ActualAtomlessLowLimit (m - 1) d ((1 - η) / 2) (c m) (C.law Gref m) mu,
      pi m = L.joint ∧ 2 < m ∧ 0 < C.s m ∧ 0 < C.a m ∧ 0 < C.h m ∧
      (∀ᵐ x ∂(L.joint.1 : Measure (LowValue d × LowValue d)),
        0 < x.2.1 ∧ x.2.1 ≤ x.1.1 ∧
        ∀ b : ℝ, 0 ≤ b →
          exactExpectedPayoff (m - 1) d ((1 - η) / 2) (c m) (C.law Gref m)
            (L.joint.1.map measurable_snd.aemeasurable) (x.1.1, b) ≤
          exactExpectedPayoff (m - 1) d ((1 - η) / 2) (c m) (C.law Gref m)
            (L.joint.1.map measurable_snd.aemeasurable) (x.1.1, x.2.1)) ∧
      (∀ b : ℝ, (realLowBidLaw L.joint.1 : Measure ℝ) {b} = 0) ∧
      EveryHigherImplementation m (c m) d η hd hη0 hη1
        (C.s m) (C.a m) (C.h m) (C.s_nonneg m) (C.a_nonneg m)
        (C.h_nonneg m) (C.total m) Gref mu L

def AllCountConclusions (C : CategoryRows) (d η : ℝ)
    (hη0 : 0 ≤ η) (hη1 : η < 1) (c : ℕ → ℕ)
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu]
    (pi : ℕ → Law (A := LowValue d) mu) : Prop :=
  ∀ (start : ℕ) (B : ℕ → BidClasses d) (H : ∀ n, HigherLaws (B n))
    (hA : ∀ n, ∀ b ∈ (B n).activeSet, d < ((1 + η) / 2) * b)
    (hP : ∀ n, ∀ b ∈ (B n).privateSet, d < b)
    (HC : ∀ n, Market.SourceHC (n + start + 1) (c (n + start + 1)) (B n) (H n)
      hη0 hη1 (hA n) (hP n)
      (C.s (n + start + 1)) (C.a (n + start + 1)) (C.h (n + start + 1))
      (C.s_nonneg (n + start + 1)) (C.a_nonneg (n + start + 1))
      (C.h_nonneg (n + start + 1)) (C.total (n + start + 1)) mu (pi (n + start + 1))),
    let Gamma := rowMarket C d η hη0 hη1 c start mu (fun n => pi (n + start + 1)) B H hA hP HC
    (∀ epsilon > 0, ∀ᶠ n in atTop, ∀ i : Fin (n + start + 1), ∀ act : JointAction 2,
      act.bid ≤ d → ((problem (Gamma n) i).outcome act).success < epsilon) ∧
    (∀ (sigmaLow : ℕ → Kernel (LowValue d) (LowValue d))
      [_hsigma : ∀ n, IsMarkovKernel (sigmaLow n)],
      ∀ w : LowValue d, ∀ i : (n : ℕ) → Fin (n + start + 1), ∀ f : Fin 3 → ℝ,
        Tendsto (fun n => (mixedCountLaw (Gamma n) (i n)
          ((sigmaLow n w).map lowBroadcast)).expect f) atTop (𝓝 (f 0))) ∧
    (∀ v : ℝ,
      (∀ᶠ n in atTop, ∀ᵐ act ∂(Gamma n).σ v, act.bid ≤ d) → ∀ f : Fin 3 → ℝ,
      Tendsto (fun n => (conditionalTypeCountLaw (Gamma n)
        (Nat.succ_pos (n + start)) v).expect f) atTop (𝓝 (f 0))) ∧
    (∀ (sigmaAction : ℕ → Kernel (LowValue d) (JointAction 2))
      [_hsigma : ∀ n, IsMarkovKernel (sigmaAction n)],
      ∀ w : LowValue d,
        (∀ᶠ n in atTop, ∀ᵐ act ∂sigmaAction n w, act.bid ≤ d) →
        ∀ i : (n : ℕ) → Fin (n + start + 1), ∀ f : Fin 3 → ℝ,
          Tendsto (fun n => (mixedCountLaw (Gamma n) (i n)
            (sigmaAction n w)).expect f) atTop (𝓝 (f 0)))

theorem triangular_primitive_endpoint
    (d η : ℝ) (hd : 0 ≤ d) (hη : 0 < η) (hη1 : η < 1)
    (C : CategoryRows) {s a h : ℝ}
    (hs : Tendsto C.s atTop (𝓝 s)) (ha : Tendsto C.a atTop (𝓝 a))
    (hh : Tendsto C.h atTop (𝓝 h)) (hs0 : 0 < s) (hh0 : 0 < h)
    (Gref : Measure ℝ) [IsProbabilityMeasure Gref]
    (c : ℕ → ℕ) (ρ : ℝ) (hlower : h / 2 < ρ) (hrank : ρ < a + h / 2)
    (hc : Tendsto (fun m => (c m : ℝ) / (m : ℝ)) atTop (𝓝 ρ))
    (hgap : 2 * Ample.binaryKL ρ (1 - h / 2) < jointRate s a h ρ)
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu]
    (hmu : ∀ᵐ w ∂mu, 0 < w.1) :
    ∃ pi : ℕ → Law (A := LowValue d) mu,
      ChosenCategoricalRows C d η hd hη.le hη1 c Gref mu pi ∧
      AllCountConclusions C d η hη.le hη1 c mu pi := by
  classical
  haveI : Nonempty (LowValue d) := nonempty_of_isProbabilityMeasure mu
  have ht := eventually_exists_triangular_general_low d η hd hη hη1
    C hs ha hh hs0 hh0 Gref c ρ hlower hrank hc hgap mu hmu
  let Q (m : ℕ) (pi : Law (A := LowValue d) mu) : Prop :=
    ∃ L : ActualAtomlessLowLimit (m - 1) d ((1 - η) / 2) (c m) (C.law Gref m) mu,
      pi = L.joint ∧ 2 < m ∧ 0 < C.s m ∧ 0 < C.a m ∧ 0 < C.h m ∧
      (∀ᵐ x ∂(L.joint.1 : Measure (LowValue d × LowValue d)),
        0 < x.2.1 ∧ x.2.1 ≤ x.1.1 ∧
        ∀ b : ℝ, 0 ≤ b →
          exactExpectedPayoff (m - 1) d ((1 - η) / 2) (c m) (C.law Gref m)
            (L.joint.1.map measurable_snd.aemeasurable) (x.1.1, b) ≤
          exactExpectedPayoff (m - 1) d ((1 - η) / 2) (c m) (C.law Gref m)
            (L.joint.1.map measurable_snd.aemeasurable) (x.1.1, x.2.1)) ∧
      (∀ b : ℝ, (realLowBidLaw L.joint.1 : Measure ℝ) {b} = 0) ∧
      EveryHigherImplementation m (c m) d η hd hη.le hη1
        (C.s m) (C.a m) (C.h m) (C.s_nonneg m) (C.a_nonneg m)
        (C.h_nonneg m) (C.total m) Gref mu L
  have hQ : ∀ᶠ m in atTop, ∃ pi, Q m pi := by
    filter_upwards [ht] with m hm
    obtain ⟨L, hm2, hsm, ham, hhm, hIC, hatom, himpl⟩ := hm
    exact ⟨L.joint, L, rfl, hm2, hsm, ham, hhm, hIC, hatom, himpl⟩
  let pi : ℕ → Law (A := LowValue d) mu := fun m =>
    if hm : ∃ pi, Q m pi then Classical.choose hm else Classical.choice inferInstance
  refine ⟨pi, ?_, ?_⟩
  · filter_upwards [hQ] with m hm
    exact (show Q m (pi m) from by
      dsimp only [pi]
      rw [dif_pos hm]
      exact Classical.choose_spec hm)
  · intro start B H hA hP HC
    dsimp only
    refine ⟨triangular_uniform_counts C d η hη.le hη1 c start mu
      (fun n => pi (n + start + 1)) B H hA hP HC hd ha hh Gref ρ hc hrank, ?_, ?_, ?_⟩
    · intro sigmaLow hsigma
      letI := hsigma
      exact triangular_every_fixed_low_kernel C d η hη.le hη1 c start mu
        (fun n => pi (n + start + 1)) B H hA hP HC hd ha hh Gref ρ hc hrank sigmaLow
    · intro v hsupport f
      exact triangular_actual_conditional_counts C d η hη.le hη1 c start mu
        (fun n => pi (n + start + 1)) B H hA hP HC hd ha hh Gref ρ hc hrank v hsupport f
    · intro sigmaAction hsigma
      letI := hsigma
      exact triangular_every_fixed_action_kernel C d η hη.le hη1 c start mu
        (fun n => pi (n + start + 1)) B H hA hP HC hd ha hh Gref ρ hc hrank sigmaAction

theorem fixed_primitive_endpoint
    (d η : ℝ) (hd : 0 ≤ d) (hη : 0 < η) (hη1 : η < 1)
    (s a h : ℝ) (hs : 0 < s) (ha : 0 ≤ a) (hh : 0 < h) (hsum : s + a + h = 1)
    (Gref : Measure ℝ) [IsProbabilityMeasure Gref]
    (c : ℕ → ℕ) (ρ : ℝ) (hlower : h / 2 < ρ) (hrank : ρ < a + h / 2)
    (hc : Tendsto (fun m => (c m : ℝ) / (m : ℝ)) atTop (𝓝 ρ))
    (hgap : 2 * Ample.binaryKL ρ (1 - h / 2) < jointRate s a h ρ)
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu]
    (hmu : ∀ᵐ w ∂mu, 0 < w.1) :
    ∃ pi : ℕ → Law (A := LowValue d) mu,
      ChosenCategoricalRows (constantRows s a h hs.le ha hh.le hsum)
        d η hd hη.le hη1 c Gref mu pi ∧
      AllCountConclusions (constantRows s a h hs.le ha hh.le hsum)
        d η hη.le hη1 c mu pi :=
  triangular_primitive_endpoint d η hd hη hη1 (constantRows s a h hs.le ha hh.le hsum)
    tendsto_const_nhds tendsto_const_nhds tendsto_const_nhds hs hh
    Gref c ρ hlower hrank hc hgap mu hmu

theorem triangular_source_primitive_endpoint
    (d η : ℝ) (hd : 0 ≤ d) (hη : 0 < η) (hη1 : η < 1)
    (C : CategoryRows) {s a h : ℝ}
    (hs : Tendsto C.s atTop (𝓝 s)) (ha : Tendsto C.a atTop (𝓝 a))
    (hh : Tendsto C.h atTop (𝓝 h)) (hs0 : 0 < s) (hh0 : 0 < h)
    (c : ℕ → ℕ) (ρ : ℝ) (hlower : h / 2 < ρ) (hrank : ρ < a + h / 2)
    (hc : Tendsto (fun m => (c m : ℝ) / (m : ℝ)) atTop (𝓝 ρ))
    (hgap : 2 * Ample.binaryKL ρ (1 - h / 2) < jointRate s a h ρ)
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu]
    (hmu : ∀ᵐ w ∂mu, 0 < w.1) :
    ∃ pi : ℕ → Law (A := LowValue d) mu,
      ChosenCategoricalRows C d η hd hη.le hη1 c (Measure.dirac (0 : ℝ)) mu pi ∧
      AllCountConclusions C d η hη.le hη1 c mu pi :=
  triangular_primitive_endpoint d η hd hη hη1 C hs ha hh hs0 hh0
    (Measure.dirac (0 : ℝ)) c ρ hlower hrank hc hgap mu hmu

theorem fixed_source_primitive_endpoint
    (d η : ℝ) (hd : 0 ≤ d) (hη : 0 < η) (hη1 : η < 1)
    (s a h : ℝ) (hs : 0 < s) (ha : 0 ≤ a) (hh : 0 < h) (hsum : s + a + h = 1)
    (c : ℕ → ℕ) (ρ : ℝ) (hlower : h / 2 < ρ) (hrank : ρ < a + h / 2)
    (hc : Tendsto (fun m => (c m : ℝ) / (m : ℝ)) atTop (𝓝 ρ))
    (hgap : 2 * Ample.binaryKL ρ (1 - h / 2) < jointRate s a h ρ)
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu]
    (hmu : ∀ᵐ w ∂mu, 0 < w.1) :
    ∃ pi : ℕ → Law (A := LowValue d) mu,
      ChosenCategoricalRows (constantRows s a h hs.le ha hh.le hsum)
        d η hd hη.le hη1 c (Measure.dirac (0 : ℝ)) mu pi ∧
      AllCountConclusions (constantRows s a h hs.le ha hh.le hsum)
        d η hη.le hη1 c mu pi :=
  fixed_primitive_endpoint d η hd hη hη1 s a h hs ha hh hsum
    (Measure.dirac (0 : ℝ)) c ρ hlower hrank hc hgap mu hmu

end FCAppendix.Appendix08.GeneralLow
