import FCAppendix.Affine.Uniform07Finishing.Native.SourceNativeRank
import FCAppendix.Affine.Uniform07Finishing.Native.LowerVersion
import FCAppendix.Affine.Hybrid.NativeLowIncentives

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing
open MeasureTheory ProbabilityTheory Game Bayes Set Filter Topology Classical
open Existence.RankEnvelope StrictNative

section Elementary
variable {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

def zeroBroadcast : JointAction 2 := ⟨0, le_rfl, 2, le_rfl⟩

theorem zeroBroadcast_payoff_nonneg (Γ : FiniteGame m 2 c Seed)
    (hg : (Γ).g = 0) (i : Fin m) {v : ℝ} (hv : 0 ≤ v) :
    0 ≤ (problem Γ i).payoff v zeroBroadcast := by
  rw [actual_zero_base_payoff Γ hg]
  simpa only [actualBidPayment, zeroBroadcast, zero_mul, sub_zero] using
    mul_nonneg hv ((problem Γ i).outcome zeroBroadcast).success_nonneg

theorem singleton_below_broadcast_best (Γ : FiniteGame m 2 c Seed)
    (R v : ℝ) (i : Fin m) (aStar : JointAction 2)
    (hB : ∀ b : JointAction 2, b.routeCount = 2 → b.bid < R →
      (problem Γ i).payoff v b ≤ (problem Γ i).payoff v aStar)
    (hS : ∀ a : JointAction 2, a.routeCount = 1 → a.bid < R →
      ∃ b : JointAction 2, b.routeCount = 2 ∧ b.bid < R ∧
        (problem Γ i).payoff v a < (problem Γ i).payoff v b)
    (a : JointAction 2) (ha : a.routeCount = 1) (hb : a.bid < R) :
    (problem Γ i).payoff v a < (problem Γ i).payoff v aStar := by
  obtain ⟨b, hk, hb', hstrict⟩ := hS a ha hb
  exact hstrict.trans_le (hB b hk hb')

end Elementary

section Source
variable {m : ℕ} [Nonempty (Fin m)]
variable (row : Uniform07.Row) (hm : 2 ≤ m) (hc : 1 ≤ Uniform07.capacity m)
    {R Λ : ℝ} (hR : 0 < R) (hUR : Early.bidCap row < R)
    (hRt : R < Uniform07.cutoff row) (hΛ : 0 < Λ)
    (PL : ProbabilityMeasure (ℝ × JointAction 2))
    (hLvalue : (PL : Measure (ℝ × JointAction 2)).map Prod.fst =
      (sourceLowerValueLaw row : Measure ℝ))
    (hLroute : ∀ᵐ x ∂(PL : Measure (ℝ × JointAction 2)),
      x.2.bid ≤ Early.bidCap row ∧ x.2.routeCount = 2)
    (α : ClassifiedContext m → unitInterval) (hα : Measurable α)

local notation "Γ" => sourceNativeGame row hc R Λ hΛ PL α hα
local notation "q" => source_upper_rank row m
local notation "t" => Uniform07.cutoff row

variable
    (hguard : error (source_upper_rank row m) (Uniform07.cutoff row) R < Uniform07.eta row * R * (1-2*sourceUpperFailure row m))
    (aT : JointAction 2) (haT : aT.routeCount = 2) (hbT : aT.bid < R)
    (hT : ∀ u : Fin m, ∀ b : JointAction 2, b.routeCount = 2 → b.bid < R →
      (problem (sourceNativeGame row hc R Λ hΛ PL α hα) u).payoff (Uniform07.cutoff row) b ≤ (problem (sourceNativeGame row hc R Λ hΛ PL α hα) u).payoff (Uniform07.cutoff row) aT)
    (hmatch : ∀ u : Fin m, (problem (sourceNativeGame row hc R Λ hΛ PL α hα) u).payoff (Uniform07.cutoff row) aT = utility (source_upper_rank row m) (Uniform07.cutoff row) R (Uniform07.cutoff row))
    (hcross : ∀ v : ℝ, 0 < v → v ≤ (Uniform07.cutoff row) → ∀ u : Fin m,
      ∀ a : JointAction 2, a.routeCount = 1 → a.bid < R →
        ∃ b : JointAction 2, b.routeCount = 2 ∧ b.bid < R ∧
          (problem (sourceNativeGame row hc R Λ hΛ PL α hα) u).payoff v a < (problem (sourceNativeGame row hc R Λ hΛ PL α hα) u).payoff v b)
    (s : ℝ) (hs : s < (source_upper_rank row m) (Uniform07.cutoff row))
    (hcap : ∀ u : Fin m, ∀ a : JointAction 2, a.bid < R →
      ((problem (sourceNativeGame row hc R Λ hΛ PL α hα) u).outcome a).success ≤ s)

include hm hR hUR hRt hLvalue hLroute hguard aT haT hbT hmatch hcross hs hcap in
theorem sourceNativeGame_lower_best_all_routes
    (v : ℝ) (hv : 0 < v) (hvt : v < t) (u : Fin m) (aStar : JointAction 2)
    (hB : ∀ b : JointAction 2, b.routeCount = 2 → b.bid < R →
      (problem Γ u).payoff v b ≤ (problem Γ u).payoff v aStar) :
    ∀ a : JointAction 2, (problem Γ u).payoff v a ≤ (problem Γ u).payoff v aStar := by
  have hnonneg : 0 ≤ (problem Γ u).payoff v aStar :=
    (zeroBroadcast_payoff_nonneg Γ rfl u hv.le).trans
      (hB zeroBroadcast rfl hR)
  have hfloor : (v-R)*q t < (problem Γ u).payoff v aStar := by
    have h := actual_lower_beats_floor_below Γ u aT hs hvt
      (hcap u aT hbT) (hmatch u)
    exact h.trans_le (hB aT haT hbT)
  intro a
  by_cases hk0 : a.routeCount = 0
  · exact (Hybrid.NativeLowIncentives.payoff_nonpos_of_zero_routes Γ u v a hk0).trans hnonneg
  have hk12 : a.routeCount = 1 ∨ a.routeCount = 2 := by
    have hk := a.routeCount_le
    omega
  by_cases hb : a.bid < R
  · rcases hk12 with hk1 | hk2
    · exact (singleton_below_broadcast_best Γ R v u aStar hB
        (hcross v hv hvt.le u) a hk1 hb).le
    · exact hB a hk2 hb
  · have hbR : R ≤ a.bid := le_of_not_gt hb
    rcases hk12 with hk1 | hk2
    · exact (sourceNativeGame_upper_singleton_below_boundary row hm hc hR hUR hRt hΛ
        PL hLvalue hLroute α hα u v hvt.le a hk1 hbR).trans hfloor.le
    · by_cases hvR : v ≤ R
      · exact (sourceNativeGame_hidden_upper_below row hm hc hR hUR hRt hΛ
          PL hLvalue hLroute α hα hguard u v hvR a hk2 hbR).le.trans hnonneg
      · exact (sourceNativeGame_hidden_upper_between row hm hc hR hUR hRt hΛ
          PL hLvalue hLroute α hα hguard u v (le_of_not_ge hvR) hvt.le a hk2 hbR).le.trans hfloor.le

include hm hR hUR hRt hLvalue hLroute hguard aT hT hmatch hcross in

theorem sourceNativeGame_boundary_all_routes (u : Fin m) :
    ∀ a : JointAction 2, (problem Γ u).payoff t a ≤ utility q t R t := by
  have hnonneg := utility_nonneg (source_upper_rank_monotone row m hm hc) hRt.le
    (source_upper_rank_bounds row m t).1 (le_rfl : t ≤ t)
  intro a
  by_cases hk0 : a.routeCount = 0
  · exact (Hybrid.NativeLowIncentives.payoff_nonpos_of_zero_routes Γ u t a hk0).trans hnonneg
  have hk12 : a.routeCount = 1 ∨ a.routeCount = 2 := by
    have hk := a.routeCount_le
    omega
  by_cases hb : a.bid < R
  · rcases hk12 with hk1 | hk2
    · exact (singleton_below_broadcast_best Γ R t u aT (hT u)
        (hcross t (Uniform07.cutoff_pos row) le_rfl u) a hk1 hb).le.trans_eq (hmatch u)
    · exact (hT u a hk2 hb).trans_eq (hmatch u)
  · have hbR : R ≤ a.bid := le_of_not_gt hb
    rcases hk12 with hk1 | hk2
    · exact sourceNativeGame_upper_one_route_bound row hm hc hR hUR hRt hΛ
        PL hLvalue hLroute α hα u t a hk1 hbR
    · exact (sourceNativeGame_hidden_upper_above row hm hc hR hUR hRt hΛ
        PL hLvalue hLroute α hα hguard u t le_rfl a hk2 hbR).le

include hm hR hUR hRt hLvalue hLroute hguard aT hT hmatch hcross hs hcap in

theorem sourceNativeGame_upper_best_all_routes (v : ℝ) (hv : t ≤ v) (u : Fin m) :
    ∀ a : JointAction 2, (problem Γ u).payoff v a ≤
      (problem Γ u).payoff v (Hybrid.upperAction (sourceUpperBid row m R) v) := by
  rw [sourceNativeGame_upper_attainment row hm hc hR hUR hRt hΛ
    PL hLvalue hLroute α hα u v hv]
  have hboundary := sourceNativeGame_boundary_all_routes row hm hc hR hUR hRt hΛ
    PL hLvalue hLroute α hα hguard aT hT hmatch hcross u
  rcases eq_or_lt_of_le hv with he | htv
  · subst v
    exact hboundary
  have hnonneg := utility_nonneg (source_upper_rank_monotone row m hm hc) hRt.le
    (source_upper_rank_bounds row m t).1 hv
  intro a
  by_cases hk0 : a.routeCount = 0
  · exact (Hybrid.NativeLowIncentives.payoff_nonpos_of_zero_routes Γ u v a hk0).trans hnonneg
  by_cases hb : a.bid < R
  · exact (upper_beats_actual_lower_above Γ u a
      (source_upper_rank_monotone row m hm hc) hs htv (hcap u a hb) (hboundary a)).le
  · have hbR : R ≤ a.bid := le_of_not_gt hb
    have hk12 : a.routeCount = 1 ∨ a.routeCount = 2 := by
      have hk := a.routeCount_le
      omega
    rcases hk12 with hk1 | hk2
    · exact sourceNativeGame_upper_one_route_bound row hm hc hR hUR hRt hΛ
        PL hLvalue hLroute α hα u v a hk1 hbR
    · exact (sourceNativeGame_hidden_upper_above row hm hc hR hUR hRt hΛ
        PL hLvalue hLroute α hα hguard u v hv a hk2 hbR).le

private theorem source_joint_action_eq_upper (a : JointAction 2)
    (b : ℝ → ℝ) (v : ℝ) (hb : 0 ≤ b v)
    (he : a.bid = b v) (hk : a.routeCount = 1) :
    a = Hybrid.upperAction b v := by
  cases a with
  | mk ab hab k hkn =>
    dsimp at he hk
    subst ab
    subst k
    simp only [Hybrid.upperAction, max_eq_left hb]

include hm hR hUR hRt hLvalue hLroute hguard aT haT hbT hT hmatch hcross hs hcap in

theorem sourceNativeGame_common_all_actions
    (hLowerIC : ∀ᵐ x ∂(PL : Measure (ℝ × JointAction 2)),
      ∀ u : Fin m, ∀ b : JointAction 2, b.routeCount = 2 → b.bid < R →
        (problem Γ u).payoff x.1 b ≤ (problem Γ u).payoff x.1 x.2) :
    ∀ᵐ x ∂(sourcePopulation row m hc R PL : Measure (ℝ × JointAction 2)),
      ∀ u : Fin m, ∀ a : JointAction 2,
        (problem Γ u).payoff x.1 a ≤ (problem Γ u).payoff x.1 x.2 := by
  have hvL : ∀ᵐ x ∂(PL : Measure (ℝ × JointAction 2)), x.1 ∈ Icc (0 : ℝ) t := by
    apply (ae_map_iff measurable_fst.aemeasurable measurableSet_Icc).mp
    rw [hLvalue]
    exact sourceLowerValueLaw_support row
  have hn0 := joint_value_ne_of_marginal PL (sourceLowerValueLaw row) hLvalue 0
  have hnt := joint_value_ne_of_marginal PL (sourceLowerValueLaw row) hLvalue t
  rw [sourcePopulation_literal, ae_add_measure_iff]
  constructor
  · apply Measure.ae_smul_measure
    filter_upwards [hvL, hn0, hnt, hLowerIC] with x hx hn0 hnt hi
    intro u
    exact sourceNativeGame_lower_best_all_routes row hm hc hR hUR hRt hΛ
      PL hLvalue hLroute α hα hguard aT haT hbT hmatch hcross s hs hcap
      x.1 (lt_of_le_of_ne hx.1 (Ne.symm hn0)) (lt_of_le_of_ne hx.2 hnt) u x.2 (hi u)
  · apply Measure.ae_smul_measure
    filter_upwards [(source_upper_joint_properties row m hm hc hR hRt).2.1] with x hx
    have he : x.2 = Hybrid.upperAction (sourceUpperBid row m R) x.1 :=
      source_joint_action_eq_upper x.2 _ x.1 (by rw [←hx.2.1]; exact hR.le.trans hx.2.2.1)
        hx.2.1 hx.2.2.2.2
    intro u a
    rw [he]
    exact sourceNativeGame_upper_best_all_routes row hm hc hR hUR hRt hΛ
      PL hLvalue hLroute α hα hguard aT hT hmatch hcross s hs hcap x.1 hx.1.1 u a

include hm hR hUR hRt hLvalue hLroute hguard aT haT hbT hT hmatch hcross hs hcap in

theorem completeSourceNativeGame_equilibrium_of_lower_chain
    (hLowerIC : ∀ᵐ x ∂(PL : Measure (ℝ × JointAction 2)),
      ∀ u : Fin m, ∀ b : JointAction 2, b.routeCount = 2 → b.bid < R →
        (problem Γ u).payoff x.1 b ≤ (problem Γ u).payoff x.1 x.2) :
    IsBayesianEquilibrium (completeSourceNativeGame row hc R Λ hΛ PL α hα) := by
  exact completeSourceNativeGame_equilibrium row hc R Λ hΛ PL α hα
    hm hR hUR hRt hLvalue hLroute
    (sourceNativeGame_common_all_actions row hm hc hR hUR hRt hΛ
      PL hLvalue hLroute α hα hguard aT haT hbT hT hmatch hcross s hs hcap hLowerIC)

end Source
end FCAppendix.Affine.Uniform07Finishing
