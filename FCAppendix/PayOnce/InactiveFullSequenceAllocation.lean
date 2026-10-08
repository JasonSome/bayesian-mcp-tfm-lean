import FCAppendix.PayOnce.InactiveFullSequenceBidGraph
import FCAppendix.PayOnce.InactiveAllocationLimit
import FCAppendix.PayOnce.ProfileExpectations

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology CommonList
open PayOnce PayOnce.CompactifiedBidLaws PayOnce.CovarianceConcentration PayOnce.KernelTailEvent
open scoped BigOperators
variable {N C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem payOnce_inactive_profile_marginal_limit
    (Γ : ∀ t, FiniteGame (N t+1) (k+1) (C t) Seed)
    (hk : 1 ≤ k) (hc : ∀ t, 0 < C t) (hcm : ∀ t, C t < N t+1)
    (hN : Tendsto N atTop atTop)
    (hA : ∀ t, (Γ t).A = Schedule.once (k+1)) (hG : ∀ t, (Γ t).G = Schedule.once (k+1))
    (hu : ∀ t, UsersOptimal (Γ t)) (B : ∀ t, PosteriorSystem (Γ t))
    (hB : ∀ t, PosteriorProposerOptimalAE (Γ t) (B t))
    (hsym : ∀ t, SymmetricProposersOnPath (Γ t))
    (hvalue : ∀ t, PositiveValueAtomless (Γ t)) (hatom : ∀ t, PositiveVisibleAtomless (Γ t))
    (hinactive : ∀ t, InactiveAbstain (Γ t))
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (hF : ∀ t, (Γ t).F = F) {g : ℝ} (hg : ∀ t, (Γ t).g = g)
    {ρ : ℝ} (hρ : Tendsto (fun t => (C t : ℝ)/(N t+1)) atTop (𝓝 ρ))
    (hρb : ρ ∈ Ioo (0:ℝ) (F.real (Ioi g))) :
    let μW := F.map (fun v => max (v-g) 0)
    let L := Limit.capRoot μW (k+1) ρ
    0 < L ∧ Limit.demand μW (k+1) L = ρ ∧
      Tendsto (fun t => ∫ d, populationMean (fun i =>
        |dummyProfileMarginal (Γ t) (by omega) d i-
          Limit.pStar (k+1) L (max ((d i).1.1-g) 0)|) ∂userProfileLaw (Γ t)) atTop (𝓝 0) := by
  obtain ⟨hL,hd,_,hgraph⟩ := payOnce_inactive_full_sequence_bid_graph Γ hk hc hcm hN hA hG hu B hB hsym hvalue hatom
    hinactive F hF hg hρ hρb
  let L := Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ
  have hM : Tendsto (fun t => N t+1) atTop atTop := (tendsto_add_atTop_nat 1).comp hN
  have hρM : Tendsto (fun t => (C t:ℝ)/((N t+1:ℕ):ℝ)) atTop (𝓝 ρ) := by
    simpa only [Nat.cast_add,Nat.cast_one] using hρ
  let p := fun t => dummyProfileMarginal (Γ t) (by omega)
  let q := fun t (d : UserProfile (N t+1) (k+1)) i => kernel (k+1) (effectiveBid (d i).1.2) L
  let r := fun t (d : UserProfile (N t+1) (k+1)) i => Limit.pStar (k+1) L (max ((d i).1.1-g) 0)
  have hp t i : Measurable (fun d => p t d i) := measurable_dummyProfileMarginal (Γ t) _ i
  have hq t i : Measurable (fun d => q t d i) := (continuous_kernel_bid (by omega) hL).measurable.comp
    (measurable_drawEffectiveBid.comp (measurable_pi_apply i))
  have hr t i : Measurable (fun d => r t d i) := (Limit.measurable_pStar (k+1) L).comp
    ((((measurable_fst.comp measurable_fst).comp (measurable_pi_apply i)).sub_const g).max measurable_const)
  have hpb t d i := dummyProfileMarginal_bounds (Γ t) (by omega) d i
  have hqb t (d : UserProfile (N t+1) (k+1)) (i : Fin (N t+1)) : q t d i ∈ Icc (0:ℝ) 1 :=
    kernel_bounds (by omega : 2 ≤ k+1) hL (effectiveBid (d i).1.2)
  have hrb t d i : r t d i ∈ Icc (0:ℝ) 1 := ⟨Limit.pStar_nonneg,Limit.pStar_le_one hL.le⟩
  have hfirst : Tendsto (fun t => ∫ d, populationMean (fun i => |p t d i-q t d i|)
      ∂userProfileLaw (Γ t)) atTop (𝓝 0) := by
    apply tendsto_of_subseq_tendsto
    intro ψ hψ
    obtain ⟨G₀,φ,hφ,hw⟩ := CompactSpace.tendsto_subseq (fun t => bidLaw (Γ (ψ t)))
    have hindex := hψ.comp hφ.tendsto_atTop
    have hh := payOnce_inactive_bid_graph_at_value_root (fun t => Γ (ψ (φ t))) hk
      (fun t => hc (ψ (φ t))) (fun t => hcm (ψ (φ t))) (hN.comp hindex)
      (fun t => hA (ψ (φ t))) (fun t => hG (ψ (φ t))) (fun t => hu (ψ (φ t)))
      (fun t => B (ψ (φ t))) (fun t => hB (ψ (φ t))) (fun t => hsym (ψ (φ t)))
      (fun t => hvalue (ψ (φ t))) (fun t => hatom (ψ (φ t)))
      (fun t => hinactive (ψ (φ t))) F (fun t => hF (ψ (φ t))) (fun t => hg (ψ (φ t)))
      (hρ.comp hindex) hρb hw
    have hload := dummy_profile_marginal_mean_L1 Γ hk hc hcm hM hA hG hu B hB hsym hvalue
      F hF hg hρM hρb.2.le
    have ha := tendsto_dummy_kernel_distance_zero (fun t => Γ (ψ (φ t))) (by omega)
      (hM.comp hindex) hw (hload.comp hindex) hh.1 hh.2.2.1
    refine ⟨φ,?_⟩
    simpa only [p,q,L,abs_sub_comm] using ha
  have hsecond : Tendsto (fun t => ∫ d, populationMean (fun i => |q t d i-r t d i|)
      ∂userProfileLaw (Γ t)) atTop (𝓝 0) := by
    apply hgraph.congr
    intro t
    symm
    apply integral_profile_mean_action (Γ t) (by omega) (K := 1)
      (fun x => |kernel (k+1) (effectiveBid x.2) L-Limit.pStar (k+1) L (max (x.1-g) 0)|)
    · exact (((continuous_kernel_bid (by omega) hL).measurable.comp
        ((measurable_effectiveBid (k+1)).comp measurable_snd)).sub
          ((Limit.measurable_pStar (k+1) L).comp ((measurable_fst.sub_const g).max measurable_const))).abs
    · intro x
      rw [Real.norm_eq_abs,abs_abs]
      exact abs_sub_le_iff.mpr ⟨by linarith [(kernel_bounds (by omega : 2 ≤ k+1) hL (effectiveBid x.2)).2,
        (Limit.pStar_nonneg : 0 ≤ Limit.pStar (k+1) L (max (x.1-g) 0))],by
        linarith [(kernel_bounds (by omega : 2 ≤ k+1) hL (effectiveBid x.2)).1,
          (Limit.pStar_le_one hL.le : Limit.pStar (k+1) L (max (x.1-g) 0) ≤ 1)]⟩
  exact ⟨hL,hd,tendsto_population_gap_of_two_gaps (fun t => userProfileLaw (Γ t)) p q r
    hp hq hr hpb hqb hrb hfirst hsecond⟩

end FCAppendix.Bayes
