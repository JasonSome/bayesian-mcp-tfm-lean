import FCAppendix.Affine.Uniform07Finishing.Native.UpperFloorReplacement
import FCAppendix.Affine.Uniform07Finishing.Native.BoundaryUtilityLimit
import FCAppendix.Affine.Uniform07Finishing.Native.SourceSuccessConstants

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing
open MeasureTheory ProbabilityTheory Game Bayes Set Filter Topology Classical
open Existence.RankEnvelope StrictNative

variable {m : ℕ}

def actualMatchedUpperFloor (row : Uniform07.Row)
    (Γ : FiniteGame m 2 (Uniform07.capacity m) unitInterval)
    (u : Fin m) (aT : JointAction 2) : ℝ :=
  Uniform07.cutoff row-(problem Γ u).payoff (Uniform07.cutoff row) aT /
    source_upper_rank row m (Uniform07.cutoff row)

theorem actualMatchedUpperFloor_matches (row : Uniform07.Row)
    (Γ : FiniteGame m 2 (Uniform07.capacity m) unitInterval)
    (hc : 1≤ Uniform07.capacity m) (u : Fin m) (aT : JointAction 2) :
    utility (source_upper_rank row m) (Uniform07.cutoff row)
      (actualMatchedUpperFloor row Γ u aT) (Uniform07.cutoff row)=
        (problem Γ u).payoff (Uniform07.cutoff row) aT := by
  rw [utility_at_floor,actualMatchedUpperFloor,sub_sub_cancel,
    div_mul_cancel₀ _ (source_upper_rank_pos row m hc _).ne']

section FixedMarket
variable [Nonempty (Fin m)]
variable (row : Uniform07.Row) (hm : 2≤ m) (hc : 1≤ Uniform07.capacity m)
  {R₀ Λ : ℝ} (hR₀ : 0< R₀) (hUR₀ : Early.bidCap row< R₀)
  (hR₀t : R₀< Uniform07.cutoff row) (hΛ : 0<Λ)
  (PL : ProbabilityMeasure (ℝ×JointAction 2))
  (hLvalue : (PL : Measure (ℝ×JointAction 2)).map Prod.fst=
    (sourceLowerValueLaw row : Measure ℝ))
  (hLroute : ∀ᵐ x ∂(PL : Measure (ℝ×JointAction 2)),
    x.2.bid≤ Early.bidCap row ∧ x.2.routeCount=2)
  (α : ClassifiedContext m→ unitInterval) (hα : Measurable α)

local notation "Γ₀" => sourceNativeGame row hc R₀ Λ hΛ PL α hα
local notation "t" => Uniform07.cutoff row
local notation "U" => Early.bidCap row

include hm hR₀ hUR₀ hR₀t hLvalue hLroute in

theorem sourceNativeGame_exists_endogenously_matched_boundary
    (u₀ : Fin m) (a₀ : JointAction 2) (ha₀U : a₀.bid≤ U) (ha₀2 : a₀.routeCount=2)
    (hCapIC : ∀ u : Fin m, ∀ b : Icc (0:ℝ) U,
      (problem Γ₀ u).payoff t (sourceLowerBroadcastAction U b)≤
        (problem Γ₀ u).payoff t a₀)
    (hIdentity : ∀ u : Fin m,
      (problem Γ₀ u).outcome a₀=(problem Γ₀ u₀).outcome a₀)
    (hR : 0< actualMatchedUpperFloor row Γ₀ u₀ a₀)
    (hUR : U< actualMatchedUpperFloor row Γ₀ u₀ a₀)
    (hRt : actualMatchedUpperFloor row Γ₀ u₀ a₀< t)
    (hpay : ∀ u : Fin m, ∀ w : ℝ×Icc (0:ℝ) U, 0<(w.2:ℝ) →
      ContinuousAt (fun y : ℝ×Icc (0:ℝ) U =>
        (problem (sourceNativeGame row hc
          (actualMatchedUpperFloor row Γ₀ u₀ a₀) Λ hΛ PL α hα) u).payoff y.1
            (sourceLowerBroadcastAction U y.2)) w)
    (hLowerIC : ∀ᵐ x ∂(PL : Measure (ℝ×JointAction 2)),
      actualBroadcastBestBelow
        (sourceNativeGame row hc (actualMatchedUpperFloor row Γ₀ u₀ a₀) Λ hΛ PL α hα)
        (actualMatchedUpperFloor row Γ₀ u₀ a₀) x.1 x.2) :
    let R := actualMatchedUpperFloor row Γ₀ u₀ a₀
    let Γ := sourceNativeGame row hc R Λ hΛ PL α hα
    ∃ aT : JointAction 2, aT.bid≤ U ∧ aT.routeCount=2 ∧
      (∀ u : Fin m, ∀ b : JointAction 2, b.routeCount=2 → b.bid< R →
        (problem Γ u).payoff t b≤(problem Γ u).payoff t aT) ∧
      (∀ u : Fin m, (problem Γ u).payoff t aT=
        utility (source_upper_rank row m) t R t) := by
  let R := actualMatchedUpperFloor row Γ₀ u₀ a₀
  let Γ := sourceNativeGame row hc R Λ hΛ PL α hα
  obtain ⟨aT,hTU,hT2,hT⟩ := sourceNativeGame_exists_boundary_broadcast_best
    row hm hc hR hUR hRt hΛ PL hLvalue hLroute α hα hpay hLowerIC
  have h₀R₀ : a₀.bid< R₀ := ha₀U.trans_lt hUR₀
  have h₀R : a₀.bid< R := ha₀U.trans_lt hUR
  have hTR₀ : aT.bid< R₀ := hTU.trans_lt hUR₀
  have hTR : aT.bid< R := hTU.trans_lt hUR
  have hinv (u : Fin m) (v : ℝ) (a : JointAction 2)
      (hk : a.routeCount=2) (hb₀ : a.bid< R₀) (hb : a.bid< R) :
      (problem Γ₀ u).payoff v a=(problem Γ u).payoff v a :=
    sourceNativeGame_lower_payoff_floor_invariant row hm hc hR₀ hUR₀ hR₀t
      hR hUR hRt hΛ PL hLvalue hLroute α hα u v a hk hb₀ hb
  have hValue := actual_boundary_utility_eq_of_outcome_invariant Γ₀ a₀ t u₀ hIdentity
  refine ⟨aT,hTU,hT2,hT,?_⟩
  intro u
  have hnew : (problem Γ u).payoff t a₀≤(problem Γ u).payoff t aT :=
    hT u a₀ ha₀2 h₀R
  have hold : (problem Γ u).payoff t aT≤(problem Γ u).payoff t a₀ := by
    rw [←hinv u t aT hT2 hTR₀ hTR,←hinv u t a₀ ha₀2 h₀R₀ h₀R]
    have h := hCapIC u ⟨aT.bid,⟨aT.bid_nonneg,hTU⟩⟩
    simpa only [sourceLowerBroadcastAction_eq U aT hTU hT2] using h
  calc
    (problem Γ u).payoff t aT=(problem Γ u).payoff t a₀ := le_antisymm hold hnew
    _=(problem Γ₀ u).payoff t a₀ := (hinv u t a₀ ha₀2 h₀R₀ h₀R).symm
    _=(problem Γ₀ u₀).payoff t a₀ := hValue u
    _=utility (source_upper_rank row m) t R t :=
      (actualMatchedUpperFloor_matches row Γ₀ hc u₀ a₀).symm

end FixedMarket

theorem actualMatchedUpperFloor_tendsto_of_moments
    (row : Uniform07.Row) (M : ℕ→ℕ) (hMtop : Tendsto M atTop atTop)
    (Γ : (k : ℕ)→ FiniteGame (M k) 2 (Uniform07.capacity (M k)) unitInterval)
    (hA : ∀ k, (Γ k).A=Schedule.affine 2 (Uniform07.eta row)
      (Uniform07.eta_pos row).le (sourceProduct_eta_le_one row))
    (hg : ∀ k, (Γ k).g=0) (u : (k : ℕ)→ Fin (M k))
    (bT : ℕ→ Icc (0:ℝ) (Early.bidCap row))
    (ε : ℕ→ℝ) (hεpos : ∀ᶠ k in atTop, 0≤ε k)
    (hε0 : Tendsto ε atTop (𝓝 0))
    (hIC : ∀ᶠ k in atTop, ∀ b : Icc (0:ℝ) (Early.bidCap row),
      (problem (Γ k) (u k)).payoff (Uniform07.cutoff row)
        (sourceLowerBroadcastAction (Early.bidCap row) b)≤
      (problem (Γ k) (u k)).payoff (Uniform07.cutoff row)
        (sourceLowerBroadcastAction (Early.bidCap row) (bT k)))
    (hmom : ∀ᶠ k in atTop, ∀ i : Fin (M k), ∀ b : Icc (0:ℝ) (Early.bidCap row),
      |((problem (Γ k) i).outcome (sourceLowerBroadcastAction (Early.bidCap row) b)).load-
        2*sourceProductProbability row b|≤ε k ∧
      |((problem (Γ k) i).outcome (sourceLowerBroadcastAction (Early.bidCap row) b)).duplicates-
        (sourceProductProbability row b)^2|≤ε k) :
    Tendsto (fun k=>actualMatchedUpperFloor row (Γ k) (u k)
      (sourceLowerBroadcastAction (Early.bidCap row) (bT k))) atTop
        (𝓝 (Uniform07.limitingFloor row)) := by
  have hu := actual_boundary_utility_tendsto_of_moments row M
    (fun k=>Uniform07.capacity (M k)) Γ hA hg u bT ε hεpos hε0 hIC hmom
  have hq := (source_upper_rank_tendsto_one row).comp hMtop
  have h := (tendsto_const_nhds (x:=Uniform07.cutoff row)).sub
    (hu.div hq (by norm_num : (1:ℝ)≠0))
  simpa only [actualMatchedUpperFloor,div_one,limiting_floor_boundary_identity,Pi.div_apply,Function.comp_apply] using h

theorem source_upper_error_le_failure (row : Uniform07.Row) (M : ℕ)
    (hM : 2≤ M) (hc : 1≤ Uniform07.capacity M) (R : ℝ)
    (hR : 0< R) (hRt : R< Uniform07.cutoff row) :
    0≤ error (source_upper_rank row M) (Uniform07.cutoff row) R ∧
      error (source_upper_rank row M) (Uniform07.cutoff row) R≤ sourceUpperFailure row M := by
  have hcm := source_capacity_lt_population M (by omega)
  have hs : ∀ᵐ v ∂upperValueMeasure row, v≤(1:ℝ) := by
    filter_upwards [ae_restrict_mem (μ:=volume) measurableSet_Icc] with v hv
    exact hv.2
  have he : M-2+1=M-1 := by omega
  have hb := Hybrid.bounded_rank_error_le (upperValueMeasure row) (M-2)
    (Uniform07.capacity M) hc (by omega) (upperValueMeasure_mass_le_one row)
    (Uniform07.cutoff row) R 1 (Uniform07.cutoff_lt_one row).le hs
  have hb' : error (source_upper_rank row M) (Uniform07.cutoff row) R≤
      (1-R)*sourceUpperFailure row M := by
    rw [he] at hb
    exact hb
  refine ⟨error_nonneg hRt.le (fun v=>(source_upper_rank_bounds row M v).2),?_⟩
  exact hb'.trans (mul_le_of_le_one_left (sourceUpperFailure_nonneg row M) (by linarith))

theorem source_common_native_guards_of_floor_limit (row : Uniform07.Row)
    (M : ℕ→ℕ) (hM : Tendsto M atTop atTop) (R : ℕ→ℝ)
    (hRlim : Tendsto R atTop (𝓝 (Uniform07.limitingFloor row))) :
    ∀ᶠ k in atTop,
      2≤ M k ∧ 1≤ Uniform07.capacity (M k) ∧
      0< R k ∧ Early.bidCap row< R k ∧ R k< Uniform07.cutoff row ∧
      R k< sourceLowerPriceCeiling row ∧
      Uniform07.kappa row*R k+Early.nativeRadius row<(27/50:ℝ)*Uniform07.cutoff row ∧
      sourceLowerSuccessCap row< source_upper_rank row (M k) (Uniform07.cutoff row) ∧
      error (source_upper_rank row (M k)) (Uniform07.cutoff row) (R k)<
        Uniform07.eta row*R k*(1-2*sourceUpperFailure row (M k)) := by
  have hU := Early.upper_floor_interface row
  have hfloor : ∀ᶠ k in atTop,
      2≤ M k ∧ 1≤ Uniform07.capacity (M k) ∧
      0< R k ∧ Early.bidCap row< R k ∧ R k< Uniform07.cutoff row := by
    filter_upwards [hM.eventually_ge_atTop 2,
      (Early.capacity_tendsto.comp hM).eventually_ge_atTop 1,
      hRlim.eventually (eventually_gt_nhds hU.2.2.1),
      hRlim.eventually (eventually_lt_nhds hU.2.2.2.1)] with k hm hc hlo hhi
    exact ⟨hm,hc,hU.2.1.trans hlo,hlo,hhi⟩
  have hE : Tendsto
      (fun k=>error (source_upper_rank row (M k)) (Uniform07.cutoff row) (R k))
      atTop (𝓝 0) := by
    apply squeeze_zero' _ _ ((sourceUpperFailure_tendsto_zero row).comp hM)
    · filter_upwards [hfloor] with k hk
      exact (source_upper_error_le_failure row (M k) hk.1 hk.2.1 (R k)
        hk.2.2.1 hk.2.2.2.2).1
    · filter_upwards [hfloor] with k hk
      exact (source_upper_error_le_failure row (M k) hk.1 hk.2.1 (R k)
        hk.2.2.1 hk.2.2.2.2).2
  have hhidden := eventually_hidden_guard_moving_floor hE
    ((sourceUpperFailure_tendsto_zero row).comp hM) hRlim
    (Uniform07.eta_pos row) (source_limiting_floor_positive row)
  have hmargin := ((hRlim.const_mul (Uniform07.kappa row)).add_const
    (Early.nativeRadius row)).eventually (eventually_lt_nhds
      (Early.kappa_limitingFloor_add_nativeRadius_lt_root_lower row))
  filter_upwards [hfloor,hhidden,hmargin,
    hRlim.eventually (eventually_lt_nhds (sourceLowerPriceCeiling_above_limit row)),
    ((source_upper_rank_tendsto_one row).comp hM).eventually
      (eventually_gt_nhds (sourceLowerSuccessCap_lt_one row))] with k hf hh hm hceil hs
  exact ⟨hf.1,hf.2.1,hf.2.2.1,hf.2.2.2.1,hf.2.2.2.2,hceil,hm,hs,hh⟩

end FCAppendix.Affine.Uniform07Finishing
