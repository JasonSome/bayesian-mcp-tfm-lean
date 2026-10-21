import FCAppendix.Existence.SingletonNativeRanks
import FCAppendix.Existence.SingletonEnvelope
import FCAppendix.Finite.SingletonDeviation
import FCAppendix.Finite.PPIRankTypes

noncomputable section
namespace FCAppendix.Bayes.SingletonConstruction
open MeasureTheory ProbabilityTheory Game Set Filter
open Existence.Singleton Existence.RankEnvelope

def ampleBid (F : Measure ℝ) (g : ℝ) (r c n : ℕ) : ℝ → ℝ :=
  singletonBid (positiveNetLaw F g) r c n

theorem ampleBid_measurable (F : Measure ℝ) [IsProbabilityMeasure F] (g : ℝ)
    [NullSingletonClass (F.restrict (Ioi g))] {r c n : ℕ} (hc : 1 ≤ c) (hn : 2 ≤ n) :
    Measurable (ampleBid F g r c n) := by
  letI := positiveNetLaw_atomless F g
  exact (continuous_singletonBid (positiveNetLaw F g) hc hn (positiveNetLaw_mass_le_one F g)).measurable

def ampleGame (r n c : ℕ) (hn : 2 ≤ n) (hc : 1 ≤ c)
    (F : Measure ℝ) [IsProbabilityMeasure F] (g : ℝ) (hg : 0 ≤ g)
    [NullSingletonClass (F.restrict (Ioi g))] (A G : Schedule n) : FiniteGame (r+2) n c Unit :=
  singletonGame (r+2) n c (by omega) F (ampleBid F g r c n)
    (ampleBid_measurable F g hc hn) A G g hg

variable {r n c : ℕ} (hn : 2 ≤ n) (hc : 1 ≤ c) (hcr : c ≤ r+1)
    (F : Measure ℝ) [IsProbabilityMeasure F] (g : ℝ) (hg : 0 ≤ g)
    [NullSingletonClass (F.restrict (Ioi g))] (A G : Schedule n)

local notation "mu" => positiveNetLaw F g
local notation "B" => ampleBid F g r c n
local notation "Gamma" => ampleGame r n c hn hc F g hg A G
local notation "q" => rank mu (r+1) c n

include hn hc

theorem ample_positiveBidMeasure_eq : positiveBidMeasure F g B=(mu).map B :=
  positiveBidMeasure_eq_net_map F g B (ampleBid_measurable F g hc hn)
    (singletonBid_nonneg mu r c n)

include hcr

theorem ample_positiveBidMeasure_atomless : NullSingletonClass (positiveBidMeasure F g B) := by
  letI := positiveNetLaw_atomless F g
  rw [ample_positiveBidMeasure_eq hn hc F g]
  exact singletonBid_atomless mu hc hcr hn (positiveNetLaw_mass_le_one F g) (positiveNetLaw_supported F g)

theorem ampleGame_acceptProb (i : Fin (r+2)) (j : Fin n) (y : ℝ) (hy : 0 ≤ y) :
    acceptProb Gamma i y j=bidRank mu (r+1) c n B y := by
  letI := ample_positiveBidMeasure_atomless hn hc hcr F g
  have hb := ampleBid_measurable (r:=r) F g hc hn
  have hmass : ((mu).map B).real univ ≤ 1 := by
    rw [map_measureReal_apply hb MeasurableSet.univ,preimage_univ]
    exact positiveNetLaw_mass_le_one F g
  have hp := contactTail_bounds ((mu).map B) hn hmass y
  change acceptProb (singletonGame (r+2) n c (by omega) F B hb A G g hg) i y j=_
  rw [singletonGame_acceptProb (by omega) F B hb A G g hg i j y hy,
    ample_positiveBidMeasure_eq hn hc F g]
  rw [show r+2-1=r+1 by omega]
  change binomBelow (r+1) (contactTail ((mu).map B) n y) c=_
  rw [binomBelow_eq_prob (r+1) c (by omega) _ hp.1 hp.2.le]
  exact (rankSuccess_eq_prob (r+1) c ⟨hp.1,hp.2.le⟩).symm

theorem ampleGame_meanAcceptProb (i : Fin (r+2)) (y : ℝ) (hy : 0 ≤ y) :
    meanAcceptProb Gamma i y=bidRank mu (r+1) c n B y := by
  unfold meanAcceptProb
  simp_rw [ampleGame_acceptProb hn hc hcr F g hg A G i _ y hy]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  rw [← mul_assoc,one_div_mul_cancel (by positivity : (n:ℝ)≠0),one_mul]

omit [NullSingletonClass (F.restrict (Ioi g))] in
theorem ampleBid_monotoneOn : MonotoneOn B (Ici 0) := by
  intro x hx y hy hxy
  rw [show B x=bid q 0 0 x from singletonBid_eq mu hc hcr hn (positiveNetLaw_mass_le_one F g) hx,
    show B y=bid q 0 0 y from singletonBid_eq mu hc hcr hn (positiveNetLaw_mass_le_one F g) hy]
  exact bid_monotoneOn (rank_monotone mu hc hcr hn (positiveNetLaw_mass_le_one F g))
    le_rfl (rank_pos mu _ _ hc hn (positiveNetLaw_mass_le_one F g) 0) hx hy hxy

theorem ampleBid_rank_at_report {w : ℝ} (hw : 0 ≤ w) :
    bidRank mu (r+1) c n B (B w)=q w := by
  letI := positiveNetLaw_atomless F g
  letI : NullSingletonClass ((mu).map B) := by
    rw [← ample_positiveBidMeasure_eq hn hc F g]
    exact ample_positiveBidMeasure_atomless hn hc hcr F g
  exact bidRank_at_report mu (ampleBid_measurable F g hc hn) hw (ampleBid_monotoneOn hn hc hcr F g)
    ((positiveNetLaw_supported F g).mono fun _ hv => hv.le) (r+1) c n

theorem ampleGame_singleton_payoff (i : Fin (r+2)) (a : JointAction n)
    (hk : a.routeCount=1) (v : ℝ) :
    (problem Gamma i).payoff v a=(v-g-a.bid)*bidRank mu (r+1) c n B a.bid := by
  rw [singleton_payoff Gamma (by omega) i a hk v,
    ampleGame_meanAcceptProb hn hc hcr F g hg A G i a.bid a.bid_nonneg]
  rfl

theorem ampleGame_played_payoff (i : Fin (r+2)) (v : ℝ) (hv : g<v) :
    (problem Gamma i).payoff v (pureAction n (by omega) g B v)=utility q 0 0 (v-g) := by
  have hk : (pureAction n (by omega) g B v).routeCount=1 := by simp [pureAction,hv]
  have hb : (pureAction n (by omega) g B v).bid=B (v-g) := by
    simp only [pureAction,if_pos hv]
    exact max_eq_left (singletonBid_nonneg mu r c n (v-g))
  rw [ampleGame_singleton_payoff hn hc hcr F g hg A G i _ hk v,hb,
    ampleBid_rank_at_report hn hc hcr F g (sub_pos.mpr hv).le]
  exact singletonBid_payoff mu hc hcr hn (positiveNetLaw_mass_le_one F g) (sub_pos.mpr hv).le

theorem ampleGame_played_success (i : Fin (r+2)) (v : ℝ) (hv : g<v) :
    ((problem Gamma i).outcome (pureAction n (by omega) g B v)).success=q (v-g) := by
  have hk : (pureAction n (by omega) g B v).routeCount=1 := by simp [pureAction,hv]
  rw [singleton_success Gamma (by omega) i _ hk,
    ampleGame_meanAcceptProb hn hc hcr F g hg A G i _ (pureAction n (by omega) g B v).bid_nonneg]
  have hb : (pureAction n (by omega) g B v).bid=B (v-g) := by
    simp only [pureAction,if_pos hv]
    exact max_eq_left (singletonBid_nonneg mu r c n (v-g))
  rw [hb,ampleBid_rank_at_report hn hc hcr F g (sub_pos.mpr hv).le]

theorem ampleGame_contact_floor (i : Fin (r+2)) (y : ℝ) (hy : 0 ≤ y) (j : Fin n) :
    q 0 ≤ acceptProb Gamma i y j := by
  rw [ampleGame_acceptProb hn hc hcr F g hg A G i j y hy]
  have hzero : B 0=0 := by
    change max (bid q 0 0 0) 0=0
    rw [bid_at_floor q 0 0 (rank_pos mu _ _ hc hn (positiveNetLaw_mass_le_one F g) 0).ne',max_self]
  have hbase := ampleBid_rank_at_report hn hc hcr F g (w:=0) le_rfl
  rw [hzero] at hbase
  rw [← hbase]
  have hb := ampleBid_measurable (r:=r) F g hc hn
  have hmass : ((mu).map B).real univ ≤ 1 := by
    rw [map_measureReal_apply hb MeasurableSet.univ,preimage_univ]
    exact positiveNetLaw_mass_le_one F g
  exact rank_monotone ((mu).map B) hc hcr hn hmass hy

end FCAppendix.Bayes.SingletonConstruction
