import FCAppendix.Exclusive.NarrowFiniteFOC
import FCAppendix.Exclusive.NarrowFiniteClassification
import FCAppendix.Exclusive.NarrowConditionalCounts

noncomputable section
namespace FCAppendix.Completion.Exclusive
open MeasureTheory ProbabilityTheory Filter Topology Set
open FCAppendix Game Bayes Exclusive Exclusive.Narrow Exclusive.Narrow.Finite
open Bayes.ExclusiveNarrow
open scoped BigOperators ProbabilityTheory

variable {m c d : ℕ} {Seed : Type*} [MeasurableSpace Seed]

def unitClamp (x : ℝ) : ℝ := max 0 (min 1 x)

theorem unitClamp_mem (x : ℝ) : unitClamp x ∈ Icc (0 : ℝ) 1 := by
  exact ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

theorem unitClamp_eq {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : unitClamp x = x := by
  rw [unitClamp, min_eq_right hx.2, max_eq_right hx.1]

theorem measurable_unitClamp : Measurable unitClamp :=
  measurable_const.max (measurable_const.min measurable_id)

theorem unitClamp_nonexpansive (x y : ℝ) :
    |unitClamp x - unitClamp y| ≤ |x-y| := by
  unfold unitClamp
  exact (abs_max_sub_max_le_max (0 : ℝ) (min 1 x) 0 (min 1 y)).trans (by
    simpa using abs_min_sub_min_le_max (1 : ℝ) x 1 y)

def corridorClamp (P : Corridor (d+1) m c) (b : ℝ) : ℝ :=
  max P.lower (min P.upper b)

theorem corridorClamp_mem (P : Corridor (d+1) m c) (b : ℝ) :
    corridorClamp P b ∈ Icc P.lower P.upper := by
  exact ⟨le_max_left _ _, max_le P.width.le (min_le_left _ _)⟩

theorem corridorClamp_eq (P : Corridor (d+1) m c) {b : ℝ}
    (hb : b ∈ Icc P.lower P.upper) : corridorClamp P b = b := by
  simp only [corridorClamp, min_eq_right hb.2, max_eq_right hb.1]

def boundedP (Γ : FiniteGame m (d+1) c Seed) (P : Corridor (d+1) m c)
    (hplay : CorridorPlay Γ P) (i : Fin m) (b : ℝ) : UserProfile m (d+1) → ℝ :=
  fun z => unitClamp ((gameRow Γ P hplay i).p (corridorClamp P b) z)

def boundedShare (Γ : FiniteGame m (d+1) c Seed) (P : Corridor (d+1) m c)
    (hplay : CorridorPlay Γ P) (i : Fin m) (b : ℝ) : UserProfile m (d+1) → ℝ :=
  fun z => unitClamp (P.share ((gameRow Γ P hplay i).weight z) (corridorClamp P b))

theorem boundedP_measurable (Γ : FiniteGame m (d+1) c Seed)
    (P : Corridor (d+1) m c) (hplay : CorridorPlay Γ P) (i : Fin m) (b : ℝ) :
    Measurable (boundedP Γ P hplay i b) :=
  measurable_unitClamp.comp ((gameRow Γ P hplay i).measurable_p _)

theorem boundedP_eq_row (Γ : FiniteGame m (d+1) c Seed)
    (P : Corridor (d+1) m c) (hplay : CorridorPlay Γ P) (i : Fin m)
    {b : ℝ} (hb : b ∈ Icc P.lower P.upper) :
    boundedP Γ P hplay i b =ᵐ[userProfileLaw Γ] (gameRow Γ P hplay i).p b := by
  filter_upwards [(gameRow Γ P hplay i).bounds] with z hz
  rw [boundedP, corridorClamp_eq P hb, unitClamp_eq]
  exact ⟨(P.allocation_bounds hz hb).1.le, (P.allocation_bounds hz hb).2⟩

theorem boundedShare_eq_row (Γ : FiniteGame m (d+1) c Seed)
    (P : Corridor (d+1) m c) (hplay : CorridorPlay Γ P) (i : Fin m)
    {b : ℝ} (hb : b ∈ Icc P.lower P.upper) :
    boundedShare Γ P hplay i b =ᵐ[userProfileLaw Γ]
      fun z => P.share ((gameRow Γ P hplay i).weight z) b := by
  filter_upwards [(gameRow Γ P hplay i).bounds] with z hz
  rw [boundedShare, corridorClamp_eq P hb, unitClamp_eq (P.share_bounds hz hb)]

theorem boundedShare_measurable (Γ : FiniteGame m (d+1) c Seed)
    (P : Corridor (d+1) m c) (hplay : CorridorPlay Γ P) (i : Fin m) (b : ℝ) :
    Measurable (boundedShare Γ P hplay i b) := by
  unfold boundedShare Corridor.share focalShare
  exact measurable_unitClamp.comp
    (measurable_const.div ((gameRow Γ P hplay i).weight_measurable.add measurable_const))

theorem boundedShare_integrable (Γ : FiniteGame m (d+1) c Seed)
    (P : Corridor (d+1) m c) (hplay : CorridorPlay Γ P) (i : Fin m) (b : ℝ) :
    Integrable (boundedShare Γ P hplay i b) (userProfileLaw Γ) := by
  apply Integrable.of_bound
    (boundedShare_measurable Γ P hplay i b).aestronglyMeasurable 1
  exact Eventually.of_forall fun z => by
    rw [Real.norm_eq_abs]
    change |unitClamp _| ≤ 1
    rw [abs_of_nonneg (unitClamp_mem _).1]
    exact (unitClamp_mem _).2

theorem boundedP_distance_integrable (Γ : FiniteGame m (d+1) c Seed)
    (P : Corridor (d+1) m c) (hplay : CorridorPlay Γ P) (i : Fin m) (b p : ℝ) :
    Integrable (fun z => |boundedP Γ P hplay i b z - p|) (userProfileLaw Γ) := by
  apply Integrable.of_bound
    ((boundedP_measurable Γ P hplay i b).sub_const p).abs.aestronglyMeasurable (1+|p|)
  exact Eventually.of_forall fun z => by
    rw [Real.norm_eq_abs, abs_abs]
    calc
      |boundedP Γ P hplay i b z-p| ≤ |boundedP Γ P hplay i b z|+|p| := by
        simpa only [sub_zero, zero_sub, abs_neg] using
          abs_sub_le (boundedP Γ P hplay i b z) 0 p
      _ ≤ 1+|p| := add_le_add (by
        change |unitClamp _| ≤ 1
        rw [abs_of_nonneg (unitClamp_mem _).1]
        exact (unitClamp_mem _).2) le_rfl

theorem differential_of_continuation (Γ : FiniteGame m (d+1) c Seed)
    (P : Corridor (d+1) m c) (hplay : CorridorPlay Γ P) (B : PosteriorSystem Γ)
    (hC : BroadcastCorridorContinuation Γ B P) (a : UserTariff)
    (hu : ExclusiveTariffUsersOptimal Γ a) (i : Fin m) (E : Set ℝ)
    (hcm : c < m)
    (hactive : userLaw Γ {u : UserDraw (d+1) | u.1.2.routeCount ≠ 0} ≠ 0) :
    FiniteBroadcastDifferential Γ a i E P.lower P.upper
      (actualMoment Γ i successIndicator) (actualCost Γ a i)
      ((gameRow Γ P hplay i).momentDerivative successIndicator)
      ((gameRow Γ P hplay i).costDerivative a Γ.G Γ.g) := by
  have D := finiteDerivativeData_of_continuation Γ P hplay B hC a hu i hcm hactive
  refine ⟨D.moment_derivative successIndicator, D.cost_derivative,
    D.success_derivative_pos, ?_⟩
  filter_upwards [D.supported_foc] with v hv
  filter_upwards [hv] with x hx _hE hfull hb
  refine ⟨?_, ?_, hx hfull hb⟩
  · simp only [actualMoment, broadcastBid_eq hfull, CountLaw.success]
  · simp only [actualCost, actualMoment, broadcastBid_eq hfull,
      UserTariff.expected, CountLaw.charge]

def countIndicator (j : ℕ) (r : ℕ) : ℝ := if r = j then 1 else 0

theorem polynomial_countIndicator (n : ℕ) (j : Fin (n+1)) {p : ℝ}
    (hp : p ∈ Icc (0 : ℝ) 1) :
    binomialPolynomial n (countIndicator j.val) p =
      PayOnce.ManyProposers.binomialMass n p j.val := by
  rw [binomialPolynomial_eq_expect n _ p hp.1 hp.2]
  have he : (fun r : Fin (n+1) => countIndicator j.val r.val) =
      (fun r => if r = j then (1 : ℝ) else 0) := by
    funext r
    simp [countIndicator, Fin.val_inj]
  rw [he, FiniteLaw.expect_singleton]
  exact binomial_mass_eq_polynomial n hp j

theorem supportedKernel_of_continuation (Γ : FiniteGame m (d+1) c Seed)
    (P : Corridor (d+1) m c) (hplay : CorridorPlay Γ P) (B : PosteriorSystem Γ)
    (hC : BroadcastCorridorContinuation Γ B P) (i : Fin m) (E : Set ℝ)
    (hband : ∀ᵐ v ∂Γ.F, ∀ᵐ x ∂Γ.σ v,
      v ∈ E → x.routeCount = d+1 → x.bid ∈ Icc P.lower P.upper) :
    SupportedActualBinomialKernel Γ i E (boundedP Γ P hplay i) := by
  refine ⟨boundedP_measurable Γ P hplay i, fun b z => unitClamp_mem _, ?_⟩
  filter_upwards [hband] with v hv
  filter_upwards [hv] with x hx hvE hfull
  intro j
  have hb := hx hvE hfull
  have he := interim_moment_of_continuation Γ P hplay B hC i (v,x)
    hfull hb (countIndicator j.val)
  have hs : (fun r : Fin (d+1+1) => countIndicator j.val r.val) =
      (fun r => if r = j then (1 : ℝ) else 0) := by
    funext r
    simp [countIndicator, Fin.val_inj]
  rw [hs, FiniteLaw.expect_singleton] at he
  rw [he]
  unfold Row.moment binomialMixtureMass
  apply integral_congr_ae
  filter_upwards [(boundedP_eq_row Γ P hplay i hb)] with z hz
  rw [← hz]
  exact polynomial_countIndicator (d+1) j (show boundedP Γ P hplay i x.bid z ∈ Icc 0 1 from unitClamp_mem _)

theorem canonical_finite_purity (Γ : FiniteGame m (d+1) c Seed)
    (P : Corridor (d+1) m c) (hplay : CorridorPlay Γ P) (B : PosteriorSystem Γ)
    (hC : BroadcastCorridorContinuation Γ B P) (a : UserTariff) (ha : a.Allowed)
    (hu : ExclusiveTariffUsersOptimal Γ a) (i : Fin m)
    (E : Set ℝ) (hE : MeasurableSet E) [NullSingletonClass (Γ.F.restrict E)]
    (hcm : c < m)
    (hactive : userLaw Γ {u : UserDraw (d+1) | u.1.2.routeCount ≠ 0} ≠ 0)
    (hband : ∀ᵐ v ∂Γ.F, ∀ᵐ x ∂Γ.σ v,
      v ∈ E → x.routeCount = d+1 ∧ x.bid ∈ Ioo P.lower P.upper) :
    ∃ beta : ℝ → ℝ, Monotone beta ∧ Measurable beta ∧
      (∀ v, beta v ∈ Icc P.lower P.upper) ∧
      (∀ᵐ v ∂Γ.F.restrict E, ∀ᵐ x ∂Γ.σ v, x.bid = beta v) := by
  obtain ⟨beta, hm, hmeas, hb, hpure, _⟩ := finite_narrow_purity_and_order
    Γ a ha hu i E hE P.lower P.upper P.width _ _ _ _
      (differential_of_continuation Γ P hplay B hC a hu i E hcm hactive) hband
  exact ⟨beta, hm, hmeas, hb, hpure⟩

theorem canonical_finite_bidLaw_no_atoms (Γ : FiniteGame m (d+1) c Seed)
    (P : Corridor (d+1) m c) (hplay : CorridorPlay Γ P) (B : PosteriorSystem Γ)
    (hC : BroadcastCorridorContinuation Γ B P) (a : UserTariff)
    (hu : ExclusiveTariffUsersOptimal Γ a) (i : Fin m)
    (E : Set ℝ) (hE : MeasurableSet E) [NullSingletonClass (Γ.F.restrict E)]
    (hcm : c < m)
    (hactive : userLaw Γ {u : UserDraw (d+1) | u.1.2.routeCount ≠ 0} ≠ 0)
    (hband : ∀ᵐ v ∂Γ.F, ∀ᵐ x ∂Γ.σ v,
      v ∈ E → x.routeCount = d+1 ∧ x.bid ∈ Ioo P.lower P.upper) :
    ∀ b : ℝ, (Measure.map (fun x : ℝ × JointAction (d+1) => x.2.bid)
      ((Γ.F.restrict E) ⊗ₘ Γ.σ)) {b} = 0 := by
  exact finite_narrow_bidLaw_no_atoms Γ a i E hE P.lower P.upper _ _ _ _
    (differential_of_continuation Γ P hplay B hC a hu i E hcm hactive) hband

theorem canonical_finite_classification (Γ : FiniteGame m (d+1) c Seed)
    (P : Corridor (d+1) m c) (hplay : CorridorPlay Γ P) (B : PosteriorSystem Γ)
    (hC : BroadcastCorridorContinuation Γ B P) (a : UserTariff) (ha : a.Allowed)
    (hu : ExclusiveTariffUsersOptimal Γ a) (i : Fin m)
    (E : Set ℝ) (hE : MeasurableSet E) [NullSingletonClass (Γ.F.restrict E)]
    (hcm : c < m)
    (hactive : userLaw Γ {u : UserDraw (d+1) | u.1.2.routeCount ≠ 0} ≠ 0)
    (hband : ∀ᵐ v ∂Γ.F, ∀ᵐ x ∂Γ.σ v,
      v ∈ E → x.routeCount = d+1 ∧ x.bid ∈ Ioo P.lower P.upper) :
    ∃ beta : ℝ → ℝ, Monotone beta ∧ Measurable beta ∧
      (∀ v, beta v ∈ Icc P.lower P.upper) ∧
      (∀ᵐ v ∂Γ.F.restrict E, ∀ᵐ x ∂Γ.σ v, x.bid = beta v) ∧
      (∃ S : Set ℝ, (Γ.F.restrict E) Sᶜ = 0 ∧ StrictMonoOn beta S) ∧
      (∀ b : ℝ, (Measure.map (fun x : ℝ × JointAction (d+1) => x.2.bid)
        ((Γ.F.restrict E) ⊗ₘ Γ.σ)) {b} = 0) := by
  obtain ⟨beta, hm, hmeas, hb, hpure, hgraph, hstrict⟩ :=
    finite_narrow_purity_and_order Γ a ha hu i E hE P.lower P.upper P.width _ _ _ _
      (differential_of_continuation Γ P hplay B hC a hu i E hcm hactive) hband
  refine ⟨beta, hm, hmeas, hb, hpure, ?_,
    canonical_finite_bidLaw_no_atoms Γ P hplay B hC a hu i E hE hcm hactive hband⟩
  let S : Set ℝ := {v | narrowBestReplyGraph Γ a i E P.lower P.upper
    (actualMoment Γ i successIndicator)
    ((gameRow Γ P hplay i).momentDerivative successIndicator)
    ((gameRow Γ P hplay i).costDerivative a Γ.G Γ.g) v (beta v)}
  refine ⟨S, ?_, ?_⟩
  · change (Γ.F.restrict E) {v | ¬ narrowBestReplyGraph Γ a i E P.lower P.upper
      (actualMoment Γ i successIndicator)
      ((gameRow Γ P hplay i).momentDerivative successIndicator)
      ((gameRow Γ P hplay i).costDerivative a Γ.G Γ.g) v (beta v)} = 0
    exact ae_iff.mp hgraph
  · intro v hv w hw hvw
    exact hstrict v w hv hw hvw

end FCAppendix.Completion.Exclusive
