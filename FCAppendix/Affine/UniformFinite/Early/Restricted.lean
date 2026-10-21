import FCAppendix.Affine.UniformFinite.FiniteAtomConstructor
import FCAppendix.Affine.UniformFinite.ExactRestrictedIC
import FCAppendix.Affine.UniformFinite.NativeOptimality

noncomputable section
namespace FCAppendix.Affine.UniformFinite
open Set MeasureTheory ProbabilityTheory Filter Topology Classical
open Existence.Distributional

structure ExactRestrictedLaw (i : Row) (M : ℕ) where
  cluster : AtomlessNoisyCluster i M
  sigma : Kernel (Value i) unitInterval
  markov : IsMarkovKernel sigma
  disintegration : lowerMeasure i⊗ₘsigma=
    (cluster.pi0.1 : Measure (Value i×unitInterval))
  IC : NoisyIC i (M-1) 0 cluster.pi0
  conditional_IC : DisintegratedNoisyIC i (M-1) 0 cluster.pi0 sigma
  cap_conull : ∀ᵐp∂(cluster.pi0.1 : Measure (Value i×unitInterval)),
    (baseBid i p:ℝ)≤ Uniform05.cap i-capSlack i
  surplus_conull : ∀ᵐp∂(cluster.pi0.1 : Measure (Value i×unitInterval)),
    (1-Uniform05.chi)*(baseBid i p:ℝ)*Lprob i M/2≤(p.1:ℝ)-(baseBid i p:ℝ)

namespace ExactRestrictedLaw
variable {i : Row} {M : ℕ}

def pi (E : ExactRestrictedLaw i M) : Joint i := E.cluster.pi0
def law (E : ExactRestrictedLaw i M) : Uniform05.RestrictedLaw i := restrictedLaw i (0,E.pi)
def physical (E : ExactRestrictedLaw i M) : Law (A:=Bid i) (lowerMeasure i) :=
  physicalLaw i (0,E.pi)
def realBid (E : ExactRestrictedLaw i M) : ProbabilityMeasure ℝ := OriginalGain.realBidLaw i 0 E.pi

instance sigma_markov (E : ExactRestrictedLaw i M) : IsMarkovKernel E.sigma := E.markov
instance bid_atomless (E : ExactRestrictedLaw i M) :
    NullSingletonClass (E.law.bidLaw : Measure (Bid i)) := by
  rw [law,restrictedLaw_bidLaw]
  exact E.cluster.bid_atomless
instance realBid_atomless (E : ExactRestrictedLaw i M) :
    NullSingletonClass (E.realBid : Measure ℝ) := E.cluster.real_bid_atomless

theorem original_marginal (E : ExactRestrictedLaw i M) :
    (E.pi.1 : Measure (Value i×unitInterval)).map Prod.fst=lowerMeasure i := E.pi.property

theorem original_real_marginal (E : ExactRestrictedLaw i M) :
    (E.law.1 : Measure (ℝ×Bid i)).map Prod.fst=Uniform05.lowerValueMeasure i := E.law.2.1

theorem physical_zero (E : ExactRestrictedLaw i M) :
    E.physical=pushLaw (lowerMeasure i) (baseBid i) (continuous_baseBid i) E.pi :=
  physicalLaw_zero i E.pi

theorem restricted_IC (E : ExactRestrictedLaw i M) : RestrictedIC i (M-1) E.pi :=
  (noisy_zero_iff_restricted_IC i (M-1) E.pi).mp E.IC

theorem conditional_all_raw_bids (E : ExactRestrictedLaw i M) :
    ∀ᵐ(v : Value i)∂lowerMeasure i,∀ᵐq∂E.sigma v,∀b : ℝ,
      b∈Icc (Uniform05.floorBid i v) (hiBid i v)→
        rawUtility i (M-1) E.law v b≤ rawUtility i (M-1) E.law v (baseBid i (v,q)) :=
  restricted_IC_disintegrated i (M-1) E.pi E.sigma E.disintegration E.restricted_IC

theorem common_conull_contract (E : ExactRestrictedLaw i M) :
    ∀ᵐp∂(E.pi.1 : Measure (Value i×unitInterval)),
      0<(p.1:ℝ) ∧ 0<(baseBid i p:ℝ) ∧
      (baseBid i p:ℝ)≤ Uniform05.cap i-capSlack i ∧
      (1-Uniform05.chi)*(baseBid i p:ℝ)*Lprob i M/2≤(p.1:ℝ)-(baseBid i p:ℝ) ∧
      ∀b : ℝ,b∈Icc (Uniform05.floorBid i p.1) (hiBid i p.1)→
        rawUtility i (M-1) E.law p.1 b≤ rawUtility i (M-1) E.law p.1 (baseBid i p) := by
  letI : NullSingletonClass ((restrictedLaw i (0,E.pi)).bidLaw : Measure (Bid i)) :=
    E.bid_atomless
  filter_upwards [original_value_positive i E.pi,ExactIC.incumbent_good i E.pi,
    E.cap_conull,E.surplus_conull,E.restricted_IC] with p hv hb hcap hsur hIC
  exact ⟨hv,hb,hcap,hsur,hIC⟩

theorem cap_support (E : ExactRestrictedLaw i M) :
    ∀ᵐ(b : Bid i)∂(E.law.bidLaw : Measure (Bid i)),(b:ℝ)≤ Uniform05.cap i-capSlack i := by
  change ∀ᵐ(b : Bid i)∂((restrictedLaw i (0,E.pi)).bidLaw : Measure (Bid i)),
    (b:ℝ)≤ Uniform05.cap i-capSlack i
  rw [← ExactIC.baseBid_map i E.pi]
  exact (ae_map_iff (continuous_baseBid i).measurable.aemeasurable
    (by measurability : MeasurableSet {b : Bid i | (b:ℝ)≤ Uniform05.cap i-capSlack i})).mpr E.cap_conull

theorem seed_singleton (E : ExactRestrictedLaw i M) :
    (E.realBid : Measure ℝ) {Uniform05.t i/2}=0 := E.cluster.seed_atom_zero

def rankMass (E : ExactRestrictedLaw i M) (b : ℝ) : ℝ :=
  Uniform05.t i*(E.realBid : Measure ℝ).real (Iic b)

def success (E : ExactRestrictedLaw i M) (b : ℝ) : ℝ := rawSuccess i (M-1) E.law b
def duplicate (E : ExactRestrictedLaw i M) (b : ℝ) : ℝ := rawDuplicate i (M-1) E.law b
def broadcastUtility (E : ExactRestrictedLaw i M) (v b : ℝ) : ℝ :=
  rawUtility i (M-1) E.law v b
def singletonUtility (E : ExactRestrictedLaw i M) (j : Fin 2) (v b : ℝ) : ℝ :=
  rawRouteUtility i (M-1) E.law j v b

end ExactRestrictedLaw

theorem eventually_exists_exact_restricted_law (i : Row) :
    ∀ᶠ M : ℕ in atTop, Nonempty (ExactRestrictedLaw i M) := by
  obtain ⟨N0,eps0,heps0,hcap⟩:=uniform_forbidden_cap_strip i
  filter_upwards [eventually_exists_atomless_noisy_cluster i,
    eventually_ge_atTop (N0+2),AtomEvents.eventually_count_geometry]
    with M hE hM hgeom
  let w:=Classical.choice hE
  have hM2 : 2≤ M:=w.market_two_le
  have hfull : M-1+1=M:=Nat.sub_add_cancel (by omega)
  letI : NullSingletonClass ((restrictedLaw i (0,w.pi0)).bidLaw : Measure (Bid i)) := by
    rw [restrictedLaw_bidLaw]
    exact w.bid_atomless
  have hIC:=actual_common_conull_restricted_IC i (M-1) w.eps w.pi w.pi0
    w.eps_tendsto w.joint_tendsto w.noisy_IC
  obtain ⟨sigma,hmark,hdis,hcond,_⟩:=disintegrate_exact_restricted_IC i (M-1) w.pi0 hIC
  have hcap0:=(hcap (M-1) (by omega) 0 (by simpa using heps0.le) w.pi0 hIC).1
  have hcapacity : 0< Uniform07.capacity M := by
    have hh:=hgeom.2.2.1
    change AtomEvents.otherLower M+1< Uniform07.capacity M at hh
    omega
  have hcost : (1+Uniform05.eta i)*(Uniform05.chi+((0:unitInterval):ℝ))≤1 := by
    cases i <;> norm_num [Uniform05.eta,Uniform05.chi,Uniform07.eta]
  have hsur:=ActualSurplus.noisyIC_common_conull_surplus i (M-1)
    (by rw [hfull]; have hh:=hgeom.1; change 2*Uniform07.capacity M+2≤ M at hh; omega)
    (by rwa [hfull]) 0
    (by have hL : 0≤ AtomEvents.lowerEvent (Uniform05.t i)
          (Uniform05.t_pos i).le (Uniform05.t_lt_one i).le M := FiniteLaw.prob_nonneg _ _
        rw [hfull]
        norm_num only [show ((0:unitInterval):ℝ)=0 by rfl]
        exact div_nonneg (mul_nonneg (by norm_num [Uniform05.chi]) hL) (by norm_num))
    hcost w.pi0 hIC
  have hsur0 : ∀ᵐp∂(w.pi0.1 : Measure (Value i×unitInterval)),
      (1-Uniform05.chi)*(baseBid i p:ℝ)*Lprob i M/2≤(p.1:ℝ)-(baseBid i p:ℝ) := by
    filter_upwards [hsur] with p hp
    simpa only [noisyBid_zero,hfull,Lprob] using hp 0
  exact ⟨⟨w,sigma,hmark,hdis,hIC,hcond,hcap0,hsur0⟩⟩

theorem exists_exact_restricted_family (i : Row) :
    ∃M0 : ℕ,∀M : ℕ,M0≤ M→ Nonempty (ExactRestrictedLaw i M) :=
  eventually_atTop.mp (eventually_exists_exact_restricted_law i)

theorem exact_restricted_multiplier_localization (i : Row) {err : ℝ} (herr : 0< err) :
    ∀ᶠM : ℕ in atTop,∀E : ExactRestrictedLaw i M,
      |E.law.multiplier-Uniform05.lambda i|< err := by
  obtain ⟨N0,eps0,heps0,h⟩:=noisy_multiplier_localization i herr
  filter_upwards [eventually_ge_atTop (N0+1)] with M hM
  intro E
  exact h (M-1) (by omega) 0 (by simpa using heps0.le) E.pi E.IC

theorem exact_restricted_cluster_active_graph (i : Row)
    (M : ℕ→ℕ) (E : ∀n,ExactRestrictedLaw i (M n)) (pi0 : Joint i)
    (hM : Tendsto M atTop atTop) (hpi : Tendsto (fun n=>(E n).pi) atTop (𝓝 pi0)) :
    (restrictedLaw i (0,pi0)).multiplier=Uniform05.lambda i ∧
    (∀ᵐp∂((restrictedLaw i (0,pi0)).1 : Measure (ℝ×Bid i)),
      (Uniform05.lambda i< p.1→(p.2:ℝ)=Uniform05.activeBid i p.1) ∧
      (p.1≤ Uniform05.lambda i→(p.2:ℝ)≤ Uniform05.lambda i)) := by
  have hN : Tendsto (fun n=> M n-1) atTop atTop := by
    apply tendsto_atTop.2
    intro k
    filter_upwards [hM.eventually_ge_atTop (k+1)] with n hn
    omega
  exact product_optimal_active_graph i (restrictedLaw i (0,pi0))
    (product_optimality_of_large_noisy_sequence i (fun n=> M n-1) (fun _=>0)
      (fun n=>(E n).pi) pi0 hN tendsto_const_nhds hpi (fun n=>(E n).IC))

end FCAppendix.Affine.UniformFinite
