import FCAppendix.Finite.PPISubcutoffBroadcast
import FCAppendix.Finite.PPINonrare
import FCAppendix.Finite.ReceiptBoundsAE

noncomputable section
namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Filter Set Topology

variable {N n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem balanced_source_actual_routed_ae
    (Γ : FiniteGame (N+1) n c Seed) (hc : 0 < c)
    (hΓ : IsAEEquilibrium Γ)
    (hfeasible : ∀ j, ProposerRationalAtFeasibleLists Γ j)
    (hvisible : VisibleAtomless Γ) (j : Fin n) (i : Fin (N+1))
    (a : ℝ) (ha : 0 < a)
    (hA : ∀ r : ℕ, 0 < r → r ≤ n → a*(r:ℝ) ≤ Γ.A.charge r) :
    (∀ᵐ d ∂userLaw Γ, 1 ≤ d.1.2.routeCount →
      0 < d.1.2.bid ∧
      (binomBelow N (alphaGt Γ j (a*d.1.2.bid)) c ≤
          meanAcceptProb Γ i d.1.2.bid ∧
        meanAcceptProb Γ i d.1.2.bid ≤
          binomBelow N (alphaGt Γ j (d.1.2.bid/a)) c) ∧
      ((problem Γ i).outcome d.1.2).load =
        d.1.2.routeCount * meanAcceptProb Γ i d.1.2.bid ∧
      (meanAcceptProb Γ i d.1.2.bid ≤ ((problem Γ i).outcome d.1.2).success ∧
        ((problem Γ i).outcome d.1.2).success ≤
          n * meanAcceptProb Γ i d.1.2.bid) ∧
      d.1.2.bid ≤ max (d.1.1-Γ.g) 0) ∧
    (∀ b : ℝ, 0 ≤ b → alphaGt Γ j b ≤ Γ.F.real (Ioi (Γ.g+b))) := by
  have hn : 0 < n := Nat.zero_lt_of_lt j.isLt
  have hpos := routed_bids_pos_of_visible_zero_atomless Γ
    (fun l => visibleBidMeasure_singleton_of_full_atomlessness Γ hvisible l 0)
  constructor
  · filter_upwards [hpos, ae_no_overbid_userLaw_onPath Γ (by omega) hc hΓ]
      with d hdpos hdover
    intro hk
    have hb := hdpos hk
    have hrank := meanAcceptProb_bounds_ae Γ hfeasible
      (VisibleAtomless.positive Γ hvisible) j i a ha hA d.1.2.bid hb
    simp only [Nat.add_sub_cancel] at hrank
    exact ⟨hb, hrank, load_eq_mean Γ hn i d.1.2,
      ⟨meanAcceptProb_le_success Γ hn i d.1.2 hk,
        success_le_n_meanAcceptProb Γ hn i d.1.2⟩, hdover hk⟩
  · exact alphaGt_le_value_tail_onPath Γ (by omega) hc hΓ j

theorem ppi_nonrare_actual_routed_uniform
    (M C : ℕ → ℕ) (Γ : ∀ k, FiniteGame (M k) n (C k) Seed)
    (F : Measure ℝ) [IsProbabilityMeasure F] [NullSingletonClass F]
    (g ρ vstar V : ℝ) (h : CongestedAssumptions M C Γ F g ρ vstar)
    (hsupport : ∀ᵐ v ∂F, v ∈ Icc 0 V)
    (hA : ∀ k, (Γ k).A = Schedule.ppi n) (i : ∀ k, Fin (M k))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ η > 0, ∀ᶠ k in atTop,
      ∀ᵐ v ∂(Γ k).F, ∀ᵐ act ∂(Γ k).σ v,
        1 ≤ act.routeCount →
        ε ≤ binomBelow (M k-1)
          (alphaGt (Γ k) (⟨0, by have hn := h.proposers_two; omega⟩ : Fin n)
            act.bid) (C k) →
        |act.bid-(vstar-g)| < η ∧ act.routeCount = 1 := by
  obtain ⟨_, hbids, hroutes, _⟩ :=
    ppi_nonrare M C Γ F g ρ vstar h hA i (V := Icc 0 V) isCompact_Icc ε hε
  intro η hη
  filter_upwards [hbids η hη, hroutes] with k hbk hrk
  have hsupportk : ∀ᵐ v ∂(Γ k).F, v ∈ Icc 0 V := by
    simpa only [h.common_values k] using hsupport
  filter_upwards [hsupportk, (h.equilibria k).users (i k)] with v hv hbr
  filter_upwards [hbr] with act hact
  intro hk hq
  exact ⟨hbk v hv act hact hk hq, hrk v hv act hact hk hq⟩

theorem ppi_source_fixed_routing_sequence
    (N C : ℕ → ℕ) (Γ : ∀ k, FiniteGame (N k+1) n (C k) Seed)
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (ρ vstar V : ℝ) (hn : 2 ≤ n) (hρ : 0 < ρ) (hscarce : (n:ℝ)*ρ < 1)
    (d : PPISubcutoffDensity F vstar V) (hcut : F.real (Ioi vstar) = (n:ℝ)*ρ)
    (hrows : ∀ k, PPISubcutoffRow (Γ k) F ρ)
    (hpop : Tendsto (fun k => N k+1) atTop atTop)
    (i : ∀ k, Fin (N k+1)) (w : ℝ) (hw0 : 0 ≤ w) (hw : w < vstar) :
    (∀ᶠ k in atTop, ∀ v : ℝ, 0 < v → v ≤ w → ∀ act : JointAction n,
      (problem (Γ k) (i k)).BestResponse v act → act.routeCount = n) ∧
    (∀ v > vstar, ∀ᶠ k in atTop, ∀ act : JointAction n,
      (problem (Γ k) (i k)).BestResponse v act → act.routeCount = 1) := by
  letI : NullSingletonClass F := d.nullSingletonClass
  have h := ppi_subcutoff_rows_nearPPI N C Γ F ρ vstar V hn hρ hscarce
    d hcut hrows hpop
  exact ⟨ppi_subcutoff_broadcast_sequence N C Γ F ρ vstar V hn hρ hscarce
      d hcut hrows hpop i w hw0 hw,
    fun v hv => h.ppi_above_cutoff_one_route i (fun k => (hrows k).ppi) v hv⟩

theorem ppi_source_broadcast_actual_draws_uniform
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (ρ vstar V : ℝ) (hn : 2 ≤ n) (hρ : 0 < ρ) (hscarce : (n:ℝ)*ρ < 1)
    (d : PPISubcutoffDensity F vstar V) (hcut : F.real (Ioi vstar) = (n:ℝ)*ρ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ m0 : ℕ, ∀ N c : ℕ, m0 ≤ N+1 → ∀ Γ : FiniteGame (N+1) n c Seed,
      PPISubcutoffRow Γ F ρ → ∀ _i : Fin (N+1),
      ∀ᵐ d ∂userLaw Γ, 0 < d.1.1 → d.1.1 ≤ vstar-ε → d.1.2.routeCount = n := by
  obtain ⟨m0,hm0⟩ := ppi_broadcast_below_cutoff_uniform (Seed := Seed)
    F ρ vstar V hn hρ hscarce d hcut ε hε
  refine ⟨m0, ?_⟩
  intro N c hN Γ hΓ i
  have hbr : ∀ᵐ d ∂userLaw Γ, (problem Γ i).BestResponse d.1.1 d.1.2 :=
    Measure.quasiMeasurePreserving_fst.ae
      (ae_bestResponse_compProd Γ hΓ.equilibrium.users i)
  filter_upwards [hbr] with draw hdraw hv hvw
  exact hm0 N c hN Γ hΓ i draw.1.1 hv hvw draw.1.2 hdraw

end FCAppendix.Bayes
