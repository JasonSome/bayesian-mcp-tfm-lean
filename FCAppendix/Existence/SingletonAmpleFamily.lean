import FCAppendix.Existence.SingletonAmpleUsers
import FCAppendix.Existence.SingletonFamily

noncomputable section
namespace FCAppendix.Bayes.SingletonConstruction
open MeasureTheory ProbabilityTheory Game Set Filter Topology
open Existence.Singleton Existence.RankEnvelope

variable {n : ℕ} (hn : 2 ≤ n) (F : Measure ℝ) [IsProbabilityMeasure F]
    (g : ℝ) (hg : 0 ≤ g) [NullSingletonClass (F.restrict (Ioi g))]
    (A G : Schedule n)

local notation "mu" => positiveNetLaw F g

include hn

omit [NullSingletonClass (F.restrict (Ioi g))] in
theorem ample_q0_tendsto_one (R C : ℕ → ℕ) (hR : Tendsto R atTop atTop)
    (hcr : ∀ t, C t ≤ R t+1) {rho : ℝ}
    (hDensity : Tendsto (fun t => (C t:ℝ)/((R t:ℝ)+2)) atTop (𝓝 rho))
    (hgap : F.real (Ioi g)/(n:ℝ)<rho) :
    Tendsto (fun t => rank mu (R t+1) (C t) n 0) atTop (𝓝 1) := by
  have hN : Tendsto (fun t => R t+1) atTop atTop := (tendsto_add_atTop_nat 1).comp hR
  have hDen : Tendsto (fun t => (C t:ℝ)/(((R t+1:ℕ):ℝ)+1)) atTop (𝓝 rho) := by
    simpa only [Nat.cast_add,Nat.cast_one,add_assoc,one_add_one_eq_two] using hDensity
  exact ample_rank_zero_tendsto_one mu hn (positiveNetLaw_mass_le_one F g) (fun t => R t+1) C
    hN (fun t => (hcr t).trans (Nat.le_succ _)) hDen
    (by rw [source_contact_at_zero mu n (positiveNetLaw_supported F g),positiveNetLaw_mass]; exact hgap)

omit [NullSingletonClass (F.restrict (Ioi g))] in
theorem ample_bid_formula {r c : ℕ} (hc : 1 ≤ c) (hcr : c ≤ r+1) {w : ℝ} (hw : 0 ≤ w) :
    ampleBid F g r c n w =
      w-(∫ x in 0..w, rank mu (r+1) c n x)/rank mu (r+1) c n w :=
  source_bid_formula mu hc hcr hn (positiveNetLaw_mass_le_one F g) hw

omit [NullSingletonClass (F.restrict (Ioi g))] in
theorem ample_bids_tendsto_uniformly_zero (R C : ℕ → ℕ) (hR : Tendsto R atTop atTop)
    (hc : ∀ t, 1 ≤ C t) (hcr : ∀ t, C t ≤ R t+1) (H : ℝ) {rho : ℝ}
    (hDensity : Tendsto (fun t => (C t:ℝ)/((R t:ℝ)+2)) atTop (𝓝 rho))
    (hgap : F.real (Ioi g)/(n:ℝ)<rho) :
    TendstoUniformlyOn (fun t w => ampleBid F g (R t) (C t) n w) (fun _ => 0) atTop (Icc 0 H) := by
  exact singleton_bids_tendsto_uniformly_zero mu hn (positiveNetLaw_mass_le_one F g) R C hR hc hcr
    (positiveNetLaw_supported F g) H hDensity (by rw [positiveNetLaw_mass]; exact hgap)

theorem exists_ample_equilibrium_family (R C : ℕ → ℕ) (hR : Tendsto R atTop atTop)
    (hc : ∀ t, 1 ≤ C t) (hcr : ∀ t, C t ≤ R t+1) {rho : ℝ}
    (hDensity : Tendsto (fun t => (C t:ℝ)/((R t:ℝ)+2)) atTop (𝓝 rho))
    (hgap : F.real (Ioi g)/(n:ℝ)<rho) (d H : ℝ) (hd0 : 0<d)
    (hd : ∀ k : ℕ, 2 ≤ k → k ≤ n → d ≤ g*(G.charge k-1))
    (hbound : ∀ᵐ v ∂F, g<v → v-g ≤ H) :
    ∃ T : ℕ, ∀ t, T ≤ t →
      UsersOptimal (ampleGame (R t) n (C t) hn (hc t) F g hg A G) ∧
      IsAEEquilibrium (ampleGame (R t) n (C t) hn (hc t) F g hg A G) ∧
      PosteriorProposerOptimalAE (ampleGame (R t) n (C t) hn (hc t) F g hg A G)
        (gamePosterior (by omega) F (ampleBid F g (R t) (C t) n)
          (ampleBid_measurable F g (hc t) hn) A G g hg) ∧
      VisibleAtomless (ampleGame (R t) n (C t) hn (hc t) F g hg A G) ∧
      (∀ j L, SymmetricAtList (ampleGame (R t) n (C t) hn (hc t) F g hg A G) L
        (seedLottery (ampleGame (R t) n (C t) hn (hc t) F g hg A G) j L)) ∧
      (∀ᵐ w ∂mu, 0<ampleBid F g (R t) (C t) n w) := by
  have hq0 := ample_q0_tendsto_one hn F g R C hR hcr hDensity hgap
  obtain ⟨T,hT⟩ := eventually_atTop.mp (eventually_costly_duplicate_gap (H:=H) hq0 hd0)
  refine ⟨T,?_⟩
  intro t ht
  letI := positiveNetLaw_atomless F g
  letI := ample_positiveBidMeasure_atomless hn (hc t) (hcr t) F g
  have hu := ampleGame_usersOptimal hn (hc t) (hcr t) F g hg A G d H hd0 hd (hT t ht) hbound
  have hp := singletonGame_proposer_optimal (m:=R t+2) (c:=C t) (by omega) F
    (ampleBid F g (R t) (C t) n) (ampleBid_measurable F g (hc t) hn) A G g hg
  exact ⟨hu,posterior_isAEEquilibrium _ hu _ hp,hp,
    singletonGame_visible_atomless (m:=R t+2) (c:=C t) (by omega) F _
      (ampleBid_measurable F g (hc t) hn) A G g hg,
    singletonGame_symmetric_at_list (by omega) F _ (ampleBid_measurable F g (hc t) hn) A G g hg,
    singletonBid_positive_ae mu (hc t) (hcr t) hn (positiveNetLaw_mass_le_one F g)
      (positiveNetLaw_supported F g)⟩

end FCAppendix.Bayes.SingletonConstruction
