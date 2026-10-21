import FCAppendix.Affine.UniformFinite.SourceAtomRates
import FCAppendix.Affine.UniformFinite.ZeroAtomLimit
import FCAppendix.Affine.UniformFinite.NoisyCompactLimit

noncomputable section
namespace FCAppendix.Affine.UniformFinite
open Set MeasureTheory ProbabilityTheory Filter Topology Classical
open Existence.Distributional

structure AtomlessNoisyCluster (i : Row) (M : ℕ) where
  eps : ℕ → unitInterval
  pi : ℕ → Joint i
  pi0 : Joint i
  sigma : ℕ → Kernel (Value i) unitInterval
  market_two_le : 2 ≤ M
  eps_pos : ∀ n, 0 < (eps n : ℝ)
  eps_source_le : ∀ n, (eps n : ℝ) ≤ PositiveClusters.noiseBound i M
  eps_tendsto : Tendsto eps atTop (𝓝 0)
  noisy_IC : ∀ n, NoisyIC i (M-1) (eps n) (pi n)
  conditional_IC : ∀ n, DisintegratedNoisyIC i (M-1) (eps n) (pi n) (sigma n)
  joint_tendsto : Tendsto pi atTop (𝓝 pi0)
  physical_tendsto :
    Tendsto (fun n => physicalLaw i (eps n,pi n)) atTop (𝓝 (physicalLaw i (0,pi0)))
  restricted_tendsto :
    Tendsto (fun n => restrictedLaw i (eps n,pi n)) atTop (𝓝 (restrictedLaw i (0,pi0)))
  base_cap : ∀ n, ∀ᵐ p ∂((pi n).1 : Measure (Value i × unitInterval)),
    (baseBid i p : ℝ) ≤ Uniform05.cap i-capSlack i
  physical_cap_common : ∀ n, ∀ᵐ p ∂((pi n).1 : Measure (Value i × unitInterval)),
    ∀ z : unitInterval, (noisyBid i (eps n,(p,z)) : ℝ) ≤ Uniform05.cap i-capSlack i/2
  physical_cap : ∀ n, ∀ᵐ (b : Bid i) ∂(bidLaw i (eps n,pi n) : Measure (Bid i)),
    (b : ℝ) ≤ Uniform05.cap i-capSlack i/2
  real_bid_atomless : NullSingletonClass (OriginalGain.realBidLaw i 0 pi0 : Measure ℝ)
  bid_atomless : NullSingletonClass (bidLaw i (0,pi0) : Measure (Bid i))

theorem sourceL_eq_Lprob (i : Row) (M : ℕ) :
    PositiveClusters.sourceL i M = Lprob i M := rfl

theorem sourceH_eq_Hprob (i : Row) (M : ℕ) :
    PositiveClusters.sourceH i M = Hprob i M := rfl

theorem sourceE_eq_Eprob (i : Row) (M : ℕ) :
    PositiveClusters.sourceE i M = Eprob i M := rfl

theorem cluster_coefficient_eq_source (i : Row) (M : ℕ)
    (hL : 0 < Lprob i M) (hH : 0 < Hprob i M) :
    PositiveClusters.lossCoefficient i M / PositiveClusters.gainCoefficient i M =
      atomCoefficient i M := by
  rw [PositiveClusters.coefficient_ratio i M hL hH]
  rfl

theorem eventually_exists_atomless_noisy_cluster (i : Row) :
    ∀ᶠ M : ℕ in atTop, Nonempty (AtomlessNoisyCluster i M) := by
  obtain ⟨N0,eps0,heps0,hcap⟩ := uniform_forbidden_cap_strip i
  filter_upwards [eventually_ge_atTop (N0+2),
    AtomEvents.eventually_count_geometry,
    eventually_source_events_positive i,atomCoefficient_eventually_small i]
    with M hM0 hgeometry hprob hsmall
  have hM2 : 2 ≤ M := by omega
  have hN0 : N0 ≤ M-1 := by omega
  have hM : M-2+2=M := Nat.sub_add_cancel hM2
  have hRivals : M-2+1=M-1 := by omega
  have hN : M-2=AtomEvents.otherLower M+2*Uniform07.capacity (M-2+2) := by
    rw [hM]
    dsimp only [AtomEvents.otherLower]
    omega
  have hroom : AtomEvents.otherLower M+1< Uniform07.capacity (M-2+2) := by
    rw [hM]
    exact hgeometry.2.2.1
  have hL : 0 < PositiveClusters.sourceL i M := hprob.1
  have hH : 0 < PositiveClusters.sourceH i M := hprob.2.1
  have hratio : PositiveClusters.lossCoefficient i M /
      PositiveClusters.gainCoefficient i M < 1/2 := by
    rw [cluster_coefficient_eq_source i M hprob.1 hprob.2.1]
    exact hsmall
  have hb : 0 < PositiveClusters.noiseBound i M :=
    PositiveClusters.noiseBound_pos i M hL
  let a : unitInterval :=
    ⟨min (1/2) (min eps0 (PositiveClusters.noiseBound i M)),
      (lt_min (by norm_num) (lt_min heps0 hb)).le,
      (min_le_left _ _).trans (by norm_num)⟩
  have ha : 0 < (a : ℝ) := lt_min (by norm_num) (lt_min heps0 hb)
  have ha_cap : (a : ℝ) ≤ eps0 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have ha_source : (a : ℝ) ≤ PositiveClusters.noiseBound i M :=
    (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨eps,pi,pi0,sigma,heps,heps_lim,hIC,hconditional,hpi,hphysical,hrestricted⟩ :=
    exists_actual_noisy_compact_limit i (M-1) a ha
  have heps_source : ∀ n, (eps n : ℝ) ≤ PositiveClusters.noiseBound i M :=
    fun n => (heps n).2.trans ha_source
  have hcap_all := fun n => hcap (M-1) hN0 (eps n)
    ((heps n).2.trans ha_cap) (pi n) (hIC n)
  have hbase : ∀ n, ∀ᵐ p ∂((pi n).1 : Measure (Value i × unitInterval)),
      (baseBid i p : ℝ) ≤ Uniform05.cap i-capSlack i :=
    fun n => (hcap_all n).1
  have hatom : NullSingletonClass (OriginalGain.realBidLaw i 0 pi0 : Measure ℝ) := by
    apply FiniteAtoms.real_atomless_of_noisy_cluster i (M-2) (AtomEvents.otherLower M)
      hN hroom (by simpa only [hM] using hL) (by simpa only [hM] using hH)
      (by simpa only [hM] using hratio) eps pi pi0
      (fun n => (heps n).1) heps_lim
      (by simpa only [hM] using heps_source)
      (by simpa only [hRivals] using hIC) hpi hbase
  exact ⟨{
    eps := eps
    pi := pi
    pi0 := pi0
    sigma := sigma
    market_two_le := hM2
    eps_pos := fun n => (heps n).1
    eps_source_le := heps_source
    eps_tendsto := heps_lim
    noisy_IC := hIC
    conditional_IC := hconditional
    joint_tendsto := hpi
    physical_tendsto := hphysical
    restricted_tendsto := hrestricted
    base_cap := hbase
    physical_cap_common := fun n => (hcap_all n).2.1
    physical_cap := fun n => (hcap_all n).2.2
    real_bid_atomless := hatom
    bid_atomless := FiniteAtoms.bid_atomless_of_real i pi0 hatom }⟩

theorem exists_atomless_noisy_cluster_family (i : Row) :
    ∃ M0 : ℕ, ∀ M : ℕ, M0 ≤ M → Nonempty (AtomlessNoisyCluster i M) := by
  exact eventually_atTop.mp (eventually_exists_atomless_noisy_cluster i)

namespace AtomlessNoisyCluster

theorem seed_atom_zero {i : Row} {M : ℕ} (w : AtomlessNoisyCluster i M) :
    (OriginalGain.realBidLaw i 0 w.pi0 : Measure ℝ) {Uniform05.t i/2}=0 :=
  FiniteAtoms.seed_atom_zero i w.pi0 w.real_bid_atomless

end AtomlessNoisyCluster
end FCAppendix.Affine.UniformFinite
