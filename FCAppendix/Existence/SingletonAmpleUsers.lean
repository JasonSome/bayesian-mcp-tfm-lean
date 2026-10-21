import FCAppendix.Existence.SingletonAmpleGame
import FCAppendix.Existence.SingletonNativeCounts
import FCAppendix.PayOnce.Participation

noncomputable section
namespace FCAppendix.Bayes.SingletonConstruction
open MeasureTheory ProbabilityTheory Game Set Filter
open Existence.Singleton Existence.RankEnvelope

variable {r n c : ℕ} (hn : 2 ≤ n) (hc : 1 ≤ c) (hcr : c ≤ r+1)
    (F : Measure ℝ) [IsProbabilityMeasure F] (g : ℝ) (hg : 0 ≤ g)
    [NullSingletonClass (F.restrict (Ioi g))] (A G : Schedule n)

local notation "mu" => positiveNetLaw F g
local notation "B" => ampleBid F g r c n
local notation "Gamma" => ampleGame r n c hn hc F g hg A G
local notation "q" => rank mu (r+1) c n

include hcr

theorem ampleGame_active_bestResponse (d H : ℝ) (hd0 : 0<d)
    (hd : ∀ k : ℕ, 2 ≤ k → k ≤ n → d ≤ g*(G.charge k-1))
    (hgap : H*(1-q 0)<d*(2*q 0-1)) (i : Fin (r+2)) (v : ℝ) (hv : g<v) (hvH : v-g ≤ H) :
    (problem Gamma i).BestResponse v (pureAction n (by omega) g B v) := by
  letI := positiveNetLaw_atomless F g
  intro a
  rw [ampleGame_played_payoff hn hc hcr F g hg A G i v hv]
  by_cases hk0 : a.routeCount=0
  · rw [payoff_zero_of_no_routes Gamma i v a hk0]
    exact (zero_utility_pos (rank_monotone mu hc hcr hn (positiveNetLaw_mass_le_one F g))
      (rank_pos mu _ _ hc hn (positiveNetLaw_mass_le_one F g) 0) (sub_pos.mpr hv)).le
  by_cases hk1 : a.routeCount=1
  · rw [ampleGame_singleton_payoff hn hc hcr F g hg A G i a hk1 v]
    exact singletonBid_all_bids_IC mu hc hcr hn (positiveNetLaw_mass_le_one F g)
      (positiveNetLaw_supported F g) (v-g) a.bid a.bid_nonneg
  have hpair := native_duplicate_probability_of_contact_floor Gamma (by omega) i a (by omega)
    (rank_bounds mu _ _ hn (positiveNetLaw_mass_le_one F g) 0).2
    (ampleGame_contact_floor hn hc hcr F g hg A G i a.bid a.bid_nonneg)
  exact (all_duplicate_routes_strictly_worse ((problem Gamma i).outcome a) A G a.bid_nonneg hg
    (sub_pos.mpr hv).le hvH hd0 (rank_bounds mu _ _ hn (positiveNetLaw_mass_le_one F g) 0).2
    (G.one (by omega)) hd hpair hgap
    (zero_utility_lower (rank_monotone mu hc hcr hn (positiveNetLaw_mass_le_one F g))
      (sub_pos.mpr hv).le)).le

omit hcr in
theorem ampleGame_inactive_bestResponse (i : Fin (r+2)) (v : ℝ) (hv : v ≤ g) :
    (problem Gamma i).BestResponse v (pureAction n (by omega) g B v) := by
  have ha : pureAction n (by omega) g B v=Interim.abstain n := by
    simp only [pureAction,if_neg (not_lt_of_ge hv)]
  rw [ha]
  intro a
  rw [Interim.Problem.payoff_abstain]
  have hh := (problem Gamma i).payoff_upper v a
  exact hh.trans_eq (max_eq_right (by change v-g ≤ 0; linarith))

theorem ampleGame_usersOptimal (d H : ℝ) (hd0 : 0<d)
    (hd : ∀ k : ℕ, 2 ≤ k → k ≤ n → d ≤ g*(G.charge k-1))
    (hgap : H*(1-q 0)<d*(2*q 0-1)) (hbound : ∀ᵐ v ∂F, g<v → v-g ≤ H) :
    UsersOptimal Gamma := by
  intro i
  filter_upwards [hbound] with v hvH
  change ∀ᵐ a ∂Measure.dirac (pureAction n (by omega) g B v), _
  rw [ae_dirac_eq]
  by_cases hv : g<v
  · exact ampleGame_active_bestResponse hn hc hcr F g hg A G d H hd0 hd hgap i v hv (hvH hv)
  · exact ampleGame_inactive_bestResponse hn hc F g hg A G i v (le_of_not_gt hv)

end FCAppendix.Bayes.SingletonConstruction
