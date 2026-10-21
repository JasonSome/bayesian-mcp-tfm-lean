import FCAppendix.Existence.SingletonGame
import FCAppendix.Existence.SingletonAmpleGame
import FCAppendix.Existence.SingletonFamily
import FCAppendix.Finite.ConditionalCountLaw
import FCAppendix.Finite.BalancedOrder

noncomputable section
namespace FCAppendix.Bayes.SingletonConstruction
open MeasureTheory ProbabilityTheory Game Set Filter
open scoped BigOperators

variable {m n c : ℕ} (hn : 0 < n) (F : Measure ℝ) [IsProbabilityMeasure F]
    (b : ℝ → ℝ) (hb : Measurable b) (A G : Schedule n) (g : ℝ) (hg : 0 ≤ g)

local notation "Gamma" => singletonGame m n c hn F b hb A G g hg

theorem singletonGame_integral_action (v : ℝ) (f : JointAction n → ℝ) :
    (∫ act, f act ∂(Gamma).σ v) = f (pureAction n hn g b v) := by
  change (∫ act, f act ∂Measure.dirac (pureAction n hn g b v)) = _
  exact integral_dirac _ _

theorem singletonGame_played_load_eq_success (i : Fin m) (v : ℝ) :
    ((problem Gamma i).outcome (pureAction n hn g b v)).load =
      ((problem Gamma i).outcome (pureAction n hn g b v)).success := by
  have hl := load_le_routeCount_mul_success Gamma i (pureAction n hn g b v)
  have hm := mul_le_mul_of_nonneg_right
    (Nat.cast_le.mpr (pureAction_route_le_one hn b g v) :
      ((pureAction n hn g b v).routeCount : ℝ) ≤ (1 : ℕ))
    (((problem Gamma i).outcome (pureAction n hn g b v)).success_nonneg)
  simp only [Nat.cast_one, one_mul] at hm
  exact le_antisymm (hl.trans hm) (CountLaw.success_le_load _)

theorem singletonGame_typeOutcome_success (i : Fin m) (v : ℝ) :
    (typeOutcome Gamma i v).success =
      ((problem Gamma i).outcome (pureAction n hn g b v)).success := by
  unfold CountLaw.success
  rw [typeOutcome_expect, singletonGame_integral_action]

theorem singletonGame_typeOutcome_load (i : Fin m) (v : ℝ) :
    (typeOutcome Gamma i v).load =
      ((problem Gamma i).outcome (pureAction n hn g b v)).load := by
  unfold CountLaw.load
  rw [typeOutcome_expect, singletonGame_integral_action]

theorem singletonGame_conditional_load_eq_success (hm : 0 < m) (v : ℝ) :
    (conditionalTypeCountLaw Gamma hm v).load =
      (conditionalTypeCountLaw Gamma hm v).success := by
  rw [conditionalTypeCountLaw_load, conditionalTypeCountLaw_success]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [singletonGame_integral_action, singletonGame_integral_action,
    singletonGame_played_load_eq_success]

theorem singletonGame_conditional_duplicates_zero (hm : 0 < m) (v : ℝ) :
    (conditionalTypeCountLaw Gamma hm v).duplicates = 0 := by
  unfold CountLaw.duplicates
  rw [singletonGame_conditional_load_eq_success, sub_self]

theorem singletonGame_finiteLoad_eq_coverage (hm : 0 < m) :
    finiteLoad Gamma = finiteCoverage Gamma := by
  rw [← integral_conditionalTypeCountLaw_load Gamma hm,
    ← integral_conditionalTypeCountLaw_success Gamma hm]
  exact integral_congr_ae (ae_of_all _ fun v =>
    singletonGame_conditional_load_eq_success hn F b hb A G g hg hm v)

theorem singletonGame_typeOutcome_success_inactive (i : Fin m) (v : ℝ) (hv : v ≤ g) :
    (typeOutcome Gamma i v).success = 0 := by
  rw [singletonGame_typeOutcome_success]
  have hr : (pureAction n hn g b v).routeCount = 0 := by
    simp [pureAction, not_lt_of_ge hv, Interim.abstain]
  have hl := load_eq_mean Gamma hn i (pureAction n hn g b v)
  rw [hr, Nat.cast_zero, zero_mul] at hl
  exact le_antisymm ((CountLaw.success_le_load _).trans_eq hl) (CountLaw.success_nonneg _)

theorem singletonGame_typeOutcome_success_active (i : Fin m) (v : ℝ) (hv : g < v) :
    (typeOutcome Gamma i v).success = meanAcceptProb Gamma i (max (b (v-g)) 0) := by
  rw [singletonGame_typeOutcome_success, ← singletonGame_played_load_eq_success,
    load_eq_mean Gamma hn i]
  simp only [pureAction, if_pos hv, Nat.cast_one, one_mul]

end FCAppendix.Bayes.SingletonConstruction

namespace FCAppendix.Bayes.SingletonConstruction
open MeasureTheory ProbabilityTheory Game Set Filter Topology
open Existence.Singleton Existence.RankEnvelope
open scoped BigOperators

variable {r n c : ℕ} (hn : 2 ≤ n) (hc : 1 ≤ c) (hcr : c ≤ r+1)
    (F : Measure ℝ) [IsProbabilityMeasure F] (g : ℝ) (hg : 0 ≤ g)
    [NullSingletonClass (F.restrict (Ioi g))] (A G : Schedule n)

local notation "mu" => positiveNetLaw F g
local notation "Gamma" => ampleGame r n c hn hc F g hg A G

include hcr in
theorem ampleGame_conditional_success (v : ℝ) :
    (conditionalTypeCountLaw Gamma (by omega) v).success =
      if g<v then rank mu (r+1) c n (v-g) else 0 := by
  rw [conditionalTypeCountLaw_success]
  have haction (i : Fin (r+2)) : (∫ act, ((problem Gamma i).outcome act).success ∂(Gamma).σ v) =
      ((problem Gamma i).outcome (pureAction n (by omega) g (ampleBid F g r c n) v)).success :=
    singletonGame_integral_action (by omega) F _ _ A G g hg v _
  simp_rw [haction]
  by_cases hv : g<v
  · simp_rw [ampleGame_played_success hn hc hcr F g hg A G _ v hv]
    simp only [if_pos hv,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    exact mul_div_cancel_left₀ _ (by positivity : ((r+2:ℕ):ℝ)≠0)
  · have he (i : Fin (r+2)) :
        ((problem Gamma i).outcome (pureAction n (by omega) g (ampleBid F g r c n) v)).success=0 := by
      have hh : (typeOutcome Gamma i v).success=0 :=
        singletonGame_typeOutcome_success_inactive (by omega) F _ _ A G g hg i v
          (le_of_not_gt hv)
      have heq : (typeOutcome Gamma i v).success =
          ((problem Gamma i).outcome (pureAction n (by omega) g (ampleBid F g r c n) v)).success :=
        singletonGame_typeOutcome_success (by omega) F _ _ A G g hg i v
      exact heq.symm.trans hh
    simp_rw [he]
    simp [hv]

include hcr in
theorem ampleGame_finiteCoverage :
    finiteCoverage Gamma = ∫ w, rank mu (r+1) c n w ∂mu := by
  rw [← integral_conditionalTypeCountLaw_success Gamma (by omega)]
  simp_rw [ampleGame_conditional_success hn hc hcr F g hg A G]
  have hq : Continuous (rank mu (r+1) c n) := by
    letI := positiveNetLaw_atomless F g
    exact continuous_rank mu _ _ _
  have hm := integral_map (μ := F.restrict (Ioi g))
    (φ := fun v : ℝ => v-g) (f := rank mu (r+1) c n)
    (measurable_id.sub_const g).aemeasurable hq.aestronglyMeasurable
  change (∫ v, if g<v then rank mu (r+1) c n (v-g) else 0 ∂F) = _
  have hm' : (∫ w, rank mu (r+1) c n w ∂mu) =
      ∫ v in Ioi g, rank mu (r+1) c n (v-g) ∂F := hm
  rw [hm']
  rw [← integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  exact ae_of_all _ fun v => by simp [Set.indicator,mem_Ioi]

include hcr in
theorem ampleGame_finiteLoad :
    finiteLoad Gamma = ∫ w, rank mu (r+1) c n w ∂mu := by
  have hh : finiteLoad Gamma = finiteCoverage Gamma :=
    singletonGame_finiteLoad_eq_coverage (by omega) F _ _ A G g hg (by omega)
  rw [hh,ampleGame_finiteCoverage hn hc hcr F g hg A G]

theorem ampleGame_conditional_duplicates_zero (v : ℝ) :
    (conditionalTypeCountLaw Gamma (by omega) v).duplicates=0 :=
  singletonGame_conditional_duplicates_zero (by omega) F _ _ A G g hg (by omega) v

end FCAppendix.Bayes.SingletonConstruction

namespace FCAppendix.Bayes.SingletonConstruction
open MeasureTheory ProbabilityTheory Game Set Filter Topology
open Existence.Singleton Existence.RankEnvelope

variable {n : ℕ} (hn : 2 ≤ n) (F : Measure ℝ) [IsProbabilityMeasure F]
    (g : ℝ) (hg : 0 ≤ g) [NullSingletonClass (F.restrict (Ioi g))]
    (A G : Schedule n)

local notation "mu" => positiveNetLaw F g

theorem ampleGame_coverage_tendsto (R C : ℕ → ℕ) (hR : Tendsto R atTop atTop)
    (hc : ∀ t, 1 ≤ C t) (hcr : ∀ t, C t ≤ R t+1) {rho : ℝ}
    (hDensity : Tendsto (fun t => (C t:ℝ)/((R t:ℝ)+2)) atTop (𝓝 rho))
    (hgap : F.real (Ioi g)/(n:ℝ)<rho) :
    Tendsto (fun t => finiteCoverage (ampleGame (R t) n (C t) hn (hc t) F g hg A G))
      atTop (𝓝 (F.real (Ioi g))) := by
  letI := positiveNetLaw_atomless F g
  have hh := singleton_integral_success_tendsto mu hn (positiveNetLaw_mass_le_one F g)
    R C hR hc hcr (positiveNetLaw_supported F g) hDensity
    (by rw [positiveNetLaw_mass]; exact hgap)
  have he : (fun t => finiteCoverage (ampleGame (R t) n (C t) hn (hc t) F g hg A G)) =
      fun t => ∫ w, rank mu (R t+1) (C t) n w ∂mu :=
    funext fun t => ampleGame_finiteCoverage hn (hc t) (hcr t) F g hg A G
  rw [he]
  simpa only [positiveNetLaw_mass] using hh

theorem ampleGame_load_tendsto (R C : ℕ → ℕ) (hR : Tendsto R atTop atTop)
    (hc : ∀ t, 1 ≤ C t) (hcr : ∀ t, C t ≤ R t+1) {rho : ℝ}
    (hDensity : Tendsto (fun t => (C t:ℝ)/((R t:ℝ)+2)) atTop (𝓝 rho))
    (hgap : F.real (Ioi g)/(n:ℝ)<rho) :
    Tendsto (fun t => finiteLoad (ampleGame (R t) n (C t) hn (hc t) F g hg A G))
      atTop (𝓝 (F.real (Ioi g))) := by
  have he : (fun t => finiteLoad (ampleGame (R t) n (C t) hn (hc t) F g hg A G)) =
      fun t => finiteCoverage (ampleGame (R t) n (C t) hn (hc t) F g hg A G) := by
    funext t
    exact singletonGame_finiteLoad_eq_coverage (by omega) F _ _ A G g hg (by omega)
  rw [he]
  exact ampleGame_coverage_tendsto hn F g hg A G R C hR hc hcr hDensity hgap

theorem ampleGame_duplicates_zero (r c : ℕ) (hc : 1 ≤ c) :
    finiteLoad (ampleGame r n c hn hc F g hg A G) -
      finiteCoverage (ampleGame r n c hn hc F g hg A G)=0 := by
  have hh : finiteLoad (ampleGame r n c hn hc F g hg A G) =
      finiteCoverage (ampleGame r n c hn hc F g hg A G) :=
    singletonGame_finiteLoad_eq_coverage (by omega) F _ _ A G g hg (by omega)
  exact sub_eq_zero.mpr hh

end FCAppendix.Bayes.SingletonConstruction
