import FCAppendix.AppendixRepair.GeneralLow.FiniteEndpoint
import FCAppendix.AppendixRepair.TriangularLow

set_option maxHeartbeats 2000000
noncomputable section
namespace FCAppendix.Appendix08.GeneralLow
open MeasureTheory ProbabilityTheory Set Filter Topology Game Bayes
open Affine Affine.LowBody Affine.Hybrid Existence.Distributional
open Affine.AppendixRepair.TriangularLow

def EveryHigherImplementation (m c : ℕ) (d η : ℝ) (hd : 0 ≤ d)
    (hη0 : 0 ≤ η) (hη1 : η < 1)
    (s a h : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ a) (hh : 0 ≤ h) (hsum : s + a + h = 1)
    (Gref : Measure ℝ) [IsProbabilityMeasure Gref]
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu]
    (L : ActualAtomlessLowLimit (m - 1) d ((1 - η) / 2) c
      (categoryLaw s a h hs ha hh hsum Gref) mu) : Prop :=
  ∀ (B : BidClasses d) (H : HigherLaws B)
    (hA : ∀ b ∈ B.activeSet, d < ((1 + η) / 2) * b)
    (hP : ∀ b ∈ B.privateSet, d < b)
    (HC : Market.SourceHC m c B H hη0 hη1 hA hP s a h hs ha hh hsum mu L.joint),
    Conclusions
      (Market.game m c B H hη0 hη1 hA hP s a h hs ha hh hsum mu L.joint HC)
      (referenceMarket m c B hd H η hη0 hη1 s a h hs ha hh hsum mu L.joint)
      (Market.belief m c B H hη0 hη1 hA hP s a h hs ha hh hsum mu L.joint HC)
      (lowJoint mu L.joint) (categoryLaw s a h hs ha hh hsum Gref) d

theorem eventually_exists_triangular_general_low
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
    ∀ᶠ m : ℕ in atTop,
      ∃ L : ActualAtomlessLowLimit (m - 1) d ((1 - η) / 2) (c m) (C.law Gref m) mu,
        2 < m ∧ 0 < C.s m ∧ 0 < C.a m ∧ 0 < C.h m ∧
        (∀ᵐ x ∂(L.joint.1 : Measure (LowValue d × LowValue d)),
          0 < x.2.1 ∧ x.2.1 ≤ x.1.1 ∧
          ∀ b : ℝ, 0 ≤ b →
            exactExpectedPayoff (m - 1) d ((1 - η) / 2) (c m) (C.law Gref m)
              (L.joint.1.map measurable_snd.aemeasurable) (x.1.1, b) ≤
            exactExpectedPayoff (m - 1) d ((1 - η) / 2) (c m) (C.law Gref m)
              (L.joint.1.map measurable_snd.aemeasurable) (x.1.1, x.2.1)) ∧
        (∀ b : ℝ, (realLowBidLaw L.joint.1 : Measure ℝ) {b} = 0) ∧
        EveryHigherImplementation m (c m) d η hd hη.le hη1
          (C.s m) (C.a m) (C.h m) (C.s_nonneg m) (C.a_nonneg m) (C.h_nonneg m)
          (C.total m) Gref mu L := by
  have hρ : 0 < ρ := (half_pos hh0).trans hlower
  have ha0 : 0 < a := by linarith
  let ξ := (1 - η) / 2
  have hξ : 0 < ξ := by dsimp [ξ]; linarith
  have hξh : ξ ≤ 1 / 2 := by dsimp [ξ]; linarith
  have hlow := Affine.AppendixRepair.TriangularLow.eventually_exists_actual_low_bid_equilibrium
    hd hξ hξh C hs ha hh hs0 hh0 Gref c ρ hρ hrank hc hgap mu hmu
  have hguards := Affine.AppendixRepair.TriangularLow.eventually_primitive_source_guards
    C hs ha hh hs0 hh0 Gref c ρ η hρ hrank hη.le hc hgap
  filter_upwards [hlow, hguards, ha.eventually_const_lt ha0, hh.eventually_const_lt hh0]
    with m hmL hmG ham hhm
  obtain ⟨L, hIC⟩ := hmL
  obtain ⟨hsm, hm2, _hcm, hell, _hboundary, hsmall, _hcoef, _huniform⟩ := hmG
  refine ⟨L, hm2, hsm, ham, hhm, ?_, ?_, ?_⟩
  · filter_upwards [L.bid_positive, L.bid_le_value, hIC] with x hx hb hopt
    exact ⟨hx, hb, hopt⟩
  · letI := L.real_atomless
    intro b
    exact measure_singleton b
  · intro B H hA hP HC
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
    exact finite_implementation B hd H hη.le hη1 hA hP
      (C.s (k + 1)) (C.a (k + 1)) (C.h (k + 1))
      (C.s_nonneg (k + 1)) (C.a_nonneg (k + 1)) (C.h_nonneg (k + 1))
      (C.total (k + 1)) Gref mu L HC hell hsmall

def constantRows (s a h : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ a) (hh : 0 ≤ h)
    (hsum : s + a + h = 1) : CategoryRows where
  s := fun _ => s
  a := fun _ => a
  h := fun _ => h
  s_nonneg := fun _ => hs
  a_nonneg := fun _ => ha
  h_nonneg := fun _ => hh
  total := fun _ => hsum

theorem eventually_exists_fixed_general_low
    (d η : ℝ) (hd : 0 ≤ d) (hη : 0 < η) (hη1 : η < 1)
    (s a h : ℝ) (hs : 0 < s) (ha : 0 ≤ a) (hh : 0 < h) (hsum : s + a + h = 1)
    (Gref : Measure ℝ) [IsProbabilityMeasure Gref]
    (c : ℕ → ℕ) (ρ : ℝ) (hlower : h / 2 < ρ) (hrank : ρ < a + h / 2)
    (hc : Tendsto (fun m => (c m : ℝ) / (m : ℝ)) atTop (𝓝 ρ))
    (hgap : 2 * Ample.binaryKL ρ (1 - h / 2) < jointRate s a h ρ)
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu]
    (hmu : ∀ᵐ w ∂mu, 0 < w.1) :
    ∀ᶠ m : ℕ in atTop,
      ∃ L : ActualAtomlessLowLimit (m - 1) d ((1 - η) / 2) (c m)
          (categoryLaw s a h hs.le ha hh.le hsum Gref) mu,
        2 < m ∧
        (∀ᵐ x ∂(L.joint.1 : Measure (LowValue d × LowValue d)),
          0 < x.2.1 ∧ x.2.1 ≤ x.1.1 ∧
          ∀ b : ℝ, 0 ≤ b →
            exactExpectedPayoff (m - 1) d ((1 - η) / 2) (c m)
              (categoryLaw s a h hs.le ha hh.le hsum Gref)
              (L.joint.1.map measurable_snd.aemeasurable) (x.1.1, b) ≤
            exactExpectedPayoff (m - 1) d ((1 - η) / 2) (c m)
              (categoryLaw s a h hs.le ha hh.le hsum Gref)
              (L.joint.1.map measurable_snd.aemeasurable) (x.1.1, x.2.1)) ∧
        (∀ b : ℝ, (realLowBidLaw L.joint.1 : Measure ℝ) {b} = 0) ∧
        EveryHigherImplementation m (c m) d η hd hη.le hη1
          s a h hs.le ha hh.le hsum Gref mu L := by
  have ht := eventually_exists_triangular_general_low d η hd hη hη1
    (constantRows s a h hs.le ha hh.le hsum)
    tendsto_const_nhds tendsto_const_nhds tendsto_const_nhds hs hh
    Gref c ρ hlower hrank hc hgap mu hmu
  filter_upwards [ht] with m hm
  obtain ⟨L, hm2, _hsm, _ham, _hhm, hIC, hatom, himpl⟩ := hm
  exact ⟨L, hm2, hIC, hatom, himpl⟩

end FCAppendix.Appendix08.GeneralLow
