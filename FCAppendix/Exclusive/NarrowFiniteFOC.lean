import FCAppendix.Exclusive.NarrowDerivativeEstimates

noncomputable section
namespace FCAppendix.Bayes.ExclusiveNarrow
open MeasureTheory ProbabilityTheory Game Exclusive Exclusive.Narrow
open Exclusive.Narrow.Finite Set Filter Topology
open scoped BigOperators ProbabilityTheory
variable {m n c k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

def broadcastBid (n : ℕ) (b : ℝ) : JointAction n :=
  ⟨max 0 b, le_max_left _ _, n, le_rfl⟩

lemma broadcastBid_eq {a : JointAction n} (ha : a.routeCount = n) :
    broadcastBid n a.bid = a := by
  cases a with
  | mk b hb k hk =>
    dsimp only at ha
    subst k
    simp only [broadcastBid, max_eq_right hb]

lemma measurable_broadcastBid (n : ℕ) : Measurable (broadcastBid n) := by
  rw [measurable_iff_comap_le]
  change MeasurableSpace.comap (broadcastBid n)
    (MeasurableSpace.comap (fun a : JointAction n => (a.bid,a.routeCount)) _) ≤ _
  rw [MeasurableSpace.comap_comp]
  exact ((measurable_const.max measurable_id).prodMk measurable_const).comap_le

def actualMoment (Γ : FiniteGame m n c Seed) (i : Fin m) (f : ℕ → ℝ) (b : ℝ) : ℝ :=
  ((problem Γ i).outcome (broadcastBid n b)).expect (fun r => f r.val)

def actualCost (Γ : FiniteGame m n c Seed) (a : UserTariff) (i : Fin m) (b : ℝ) : ℝ :=
  b * actualMoment Γ i a.charge b + Γ.g * actualMoment Γ i Γ.G.charge b

def actualObjective (Γ : FiniteGame m n c Seed) (a : UserTariff)
    (i : Fin m) (v b : ℝ) : ℝ :=
  v * actualMoment Γ i successIndicator b - actualCost Γ a i b

lemma actualObjective_eq_payoff (Γ : FiniteGame m n c Seed) (a : UserTariff)
    (i : Fin m) (v : ℝ) {b : ℝ} (hb : 0 ≤ b) :
    actualObjective Γ a i v b = exclusiveTariffPayoff Γ a i v (broadcastBid n b) := by
  simp only [actualObjective, actualCost, actualMoment, exclusiveTariffPayoff,
    UserTariff.expected, CountLaw.success, CountLaw.charge, broadcastBid, max_eq_right hb]
  ring

lemma measurable_actualMoment (Γ : FiniteGame m n c Seed) (i : Fin m) (f : ℕ → ℝ) :
    Measurable (actualMoment Γ i f) :=
  (measurable_outcome_expect Γ i (fun r => f r.val)).comp (measurable_broadcastBid n)

lemma measurable_actualCost (Γ : FiniteGame m n c Seed) (a : UserTariff) (i : Fin m) :
    Measurable (actualCost Γ a i) :=
  (measurable_id.mul (measurable_actualMoment Γ i a.charge)).add
    (measurable_const.mul (measurable_actualMoment Γ i Γ.G.charge))

lemma measurable_actualObjective (Γ : FiniteGame m n c Seed) (a : UserTariff)
    (i : Fin m) (v : ℝ) : Measurable (actualObjective Γ a i v) :=
  (measurable_const.mul (measurable_actualMoment Γ i successIndicator)).sub
    (measurable_actualCost Γ a i)

lemma actualMoment_eq_row_of_continuation (Γ : FiniteGame m (k+1) c Seed)
    (P : Corridor (k+1) m c) (hplay : CorridorPlay Γ P) (B : PosteriorSystem Γ)
    (hC : BroadcastCorridorContinuation Γ B P) (i : Fin m) (f : ℕ → ℝ)
    {b : ℝ} (hb : b ∈ Icc P.lower P.upper) :
    actualMoment Γ i f b = (gameRow Γ P hplay i).moment f b := by
  have hb0 := (P.lower_pos.trans_le hb.1).le
  simpa only [actualMoment,broadcastBid,max_eq_right hb0] using
    interim_moment_of_continuation Γ P hplay B hC i
      (0,broadcastBid (k+1) b) rfl (by simpa [broadcastBid,max_eq_right hb0] using hb) f

theorem hasDerivAt_actualMoment_of_continuation (Γ : FiniteGame m (k+1) c Seed)
    (P : Corridor (k+1) m c) (hplay : CorridorPlay Γ P) (B : PosteriorSystem Γ)
    (hC : BroadcastCorridorContinuation Γ B P) (i : Fin m) (f : ℕ → ℝ)
    {b : ℝ} (hb : b ∈ P.interior) :
    HasDerivAt (actualMoment Γ i f) ((gameRow Γ P hplay i).momentDerivative f b) b := by
  apply ((gameRow Γ P hplay i).hasDerivAt_moment f hb).congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hb.1 hb.2] with x hx
  exact actualMoment_eq_row_of_continuation Γ P hplay B hC i f ⟨hx.1.le,hx.2.le⟩

theorem hasDerivAt_actualCost_of_continuation (Γ : FiniteGame m (k+1) c Seed)
    (P : Corridor (k+1) m c) (hplay : CorridorPlay Γ P) (B : PosteriorSystem Γ)
    (hC : BroadcastCorridorContinuation Γ B P) (i : Fin m) (a : UserTariff)
    {b : ℝ} (hb : b ∈ P.interior) :
    HasDerivAt (actualCost Γ a i)
      ((gameRow Γ P hplay i).costDerivative a Γ.G Γ.g b) b := by
  apply ((gameRow Γ P hplay i).hasDerivAt_cost a Γ.G Γ.g hb).congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hb.1 hb.2] with x hx
  unfold actualCost Row.cost
  rw [actualMoment_eq_row_of_continuation Γ P hplay B hC i a.charge ⟨hx.1.le,hx.2.le⟩,
    actualMoment_eq_row_of_continuation Γ P hplay B hC i Γ.G.charge ⟨hx.1.le,hx.2.le⟩]

theorem supported_interior_FOC_of_continuation (Γ : FiniteGame m (k+1) c Seed)
    (P : Corridor (k+1) m c) (hplay : CorridorPlay Γ P) (B : PosteriorSystem Γ)
    (hC : BroadcastCorridorContinuation Γ B P) (i : Fin m) (tariff : UserTariff)
    {v : ℝ} {a : JointAction (k+1)} (ha : ExclusiveTariffBestResponse Γ tariff i v a)
    (hfull : a.routeCount = k+1) (hb : a.bid ∈ P.interior) :
    v * (gameRow Γ P hplay i).momentDerivative successIndicator a.bid =
      (gameRow Γ P hplay i).costDerivative tariff Γ.G Γ.g a.bid := by
  have hloc : IsLocalMax (actualObjective Γ tariff i v) a.bid := by
    filter_upwards [Ioo_mem_nhds hb.1 hb.2] with x hx
    rw [actualObjective_eq_payoff Γ tariff i v (P.lower_pos.trans hx.1).le,
      actualObjective_eq_payoff Γ tariff i v a.bid_nonneg, broadcastBid_eq hfull]
    exact ha (broadcastBid (k+1) x)
  have hder := ((hasDerivAt_actualMoment_of_continuation Γ P hplay B hC i
    successIndicator hb).const_mul v).sub
      (hasDerivAt_actualCost_of_continuation Γ P hplay B hC i tariff hb)
  change HasDerivAt (actualObjective Γ tariff i v) _ a.bid at hder
  have hz := hloc.deriv_eq_zero
  rw [hder.deriv] at hz
  exact sub_eq_zero.mp hz

theorem ae_supported_interior_FOC_of_continuation (Γ : FiniteGame m (k+1) c Seed)
    (P : Corridor (k+1) m c) (hplay : CorridorPlay Γ P) (B : PosteriorSystem Γ)
    (hC : BroadcastCorridorContinuation Γ B P) (tariff : UserTariff)
    (hu : ExclusiveTariffUsersOptimal Γ tariff) (i : Fin m) :
    ∀ᵐ v ∂Γ.F, ∀ᵐ a ∂Γ.σ v, a.routeCount = k+1 → a.bid ∈ P.interior →
      v * (gameRow Γ P hplay i).momentDerivative successIndicator a.bid =
        (gameRow Γ P hplay i).costDerivative tariff Γ.G Γ.g a.bid := by
  filter_upwards [hu i] with v hv
  filter_upwards [hv] with a ha hfull hb
  exact supported_interior_FOC_of_continuation Γ P hplay B hC i tariff ha hfull hb

structure FiniteDerivativeData (Γ : FiniteGame m n c Seed) (P : Corridor n m c)
    (hplay : CorridorPlay Γ P) (tariff : UserTariff) (i : Fin m) : Prop where
  moment_derivative : ∀ f b, b ∈ P.interior →
    HasDerivAt (actualMoment Γ i f) ((gameRow Γ P hplay i).momentDerivative f b) b
  cost_derivative : ∀ b, b ∈ P.interior →
    HasDerivAt (actualCost Γ tariff i) ((gameRow Γ P hplay i).costDerivative tariff Γ.G Γ.g b) b
  success_derivative_pos : ∀ b, b ∈ P.interior →
    0 < (gameRow Γ P hplay i).momentDerivative successIndicator b
  supported_foc : ∀ᵐ v ∂Γ.F, ∀ᵐ a ∂Γ.σ v, a.routeCount = n → a.bid ∈ P.interior →
    v * (gameRow Γ P hplay i).momentDerivative successIndicator a.bid =
      (gameRow Γ P hplay i).costDerivative tariff Γ.G Γ.g a.bid
  moment_error : ∀ f K b, CountTestBound n f K → b ∈ Icc P.lower P.upper →
    |(gameRow Γ P hplay i).momentDerivative f b -
      (gameRow Γ P hplay i).referenceDerivative f b| ≤
      2 * n * K * P.radius * P.ownBound

theorem finiteDerivativeData_of_continuation (Γ : FiniteGame m (k+1) c Seed)
    (P : Corridor (k+1) m c) (hplay : CorridorPlay Γ P) (B : PosteriorSystem Γ)
    (hC : BroadcastCorridorContinuation Γ B P) (tariff : UserTariff)
    (hu : ExclusiveTariffUsersOptimal Γ tariff) (i : Fin m) (hcm : c < m)
    (hactive : userLaw Γ {u : UserDraw (k+1) | u.1.2.routeCount ≠ 0} ≠ 0) :
    FiniteDerivativeData Γ P hplay tariff i where
  moment_derivative := fun f _b hb =>
    hasDerivAt_actualMoment_of_continuation Γ P hplay B hC i f hb
  cost_derivative := fun _b hb =>
    hasDerivAt_actualCost_of_continuation Γ P hplay B hC i tariff hb
  success_derivative_pos := fun _b hb =>
    (gameRow Γ P hplay i).successDerivative_pos ⟨hb.1.le,hb.2.le⟩
      (overload_positive Γ P hplay i hcm hactive)
  supported_foc := ae_supported_interior_FOC_of_continuation Γ P hplay B hC tariff hu i
  moment_error := fun f _K _b hf hb => (gameRow Γ P hplay i).derivative_error f hf hb

theorem ae_reference_foc_error (Γ : FiniteGame m n c Seed) (P : Corridor n m c)
    (hplay : CorridorPlay Γ P) (tariff : UserTariff) (htariff : tariff.Allowed) (i : Fin m)
    (D : FiniteDerivativeData Γ P hplay tariff i) :
    ∀ᵐ v ∂Γ.F, ∀ᵐ a ∂Γ.σ v, a.routeCount = n → a.bid ∈ P.interior →
      |v * (gameRow Γ P hplay i).referenceDerivative successIndicator a.bid -
        (gameRow Γ P hplay i).referenceCostDerivative tariff Γ.G Γ.g a.bid| ≤
      (2 * n * P.radius * (|v| + P.upper * n + |Γ.g| * n)) * P.ownBound := by
  filter_upwards [D.supported_foc] with v hv
  filter_upwards [hv] with a ha hfull hb
  exact (gameRow Γ P hplay i).reference_foc_error tariff htariff Γ.G Γ.g v
    ⟨hb.1.le,hb.2.le⟩ (ha hfull hb)

end FCAppendix.Bayes.ExclusiveNarrow
