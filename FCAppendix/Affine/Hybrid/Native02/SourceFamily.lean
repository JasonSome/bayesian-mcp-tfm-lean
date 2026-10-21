import FCAppendix.Affine.Hybrid.Native02.PrimitiveInput
import FCAppendix.Affine.Hybrid.Native02.NativePopulationMenus
import FCAppendix.Affine.Hybrid.Native02.UpperGraphPackage
import FCAppendix.Affine.Hybrid.Native02.UpperSource

set_option maxHeartbeats 1500000
noncomputable section
namespace FCAppendix.Affine.Hybrid.Native02
open MeasureTheory ProbabilityTheory Set Filter Topology Game Bayes Classical
open Existence.Distributional Existence.RankEnvelope

structure SourceFamily (p : PrimitiveInput) (A : FrozenActiveFamily p) where
  start : ℕ
  start_ge : A.start ≤ start
  t : ℝ
  H : ℝ
  t_mem : t ∈ p.upperSupport
  H_mem : H ∈ p.upperSupport
  Rt : p.R < t
  upperSupport_bounds : p.upperSupport ⊆ Icc t H
  capacity_valid : ∀ m ≥ start, 2 ≤ m ∧ 1 ≤ p.capacity m ∧ p.capacity m < m
  low_guards : ∀ m ≥ start,
    0 < (CommonList.iid p.categories (m-1)).prob
      (LowBody.LocalUnderflow (p.capacity m) 0) ∧
    (CommonList.iid p.categories (m-1)).prob (LowBody.BothUnderflow (p.capacity m)) ≤
      (CommonList.iid p.categories (m-1)).prob
        (LowBody.LocalUnderflow (p.capacity m) 0) / 4
  upper_guard : ∀ m ≥ start,
    error (rank (ENNReal.ofReal p.h • (p.upperValues : Measure ℝ))
      (m-1) (p.capacity m) 2) t p.R <
      p.eta*p.R*(1-2*(1-rank (ENNReal.ofReal p.h • (p.upperValues : Measure ℝ))
        (m-1) (p.capacity m) 2 t))

theorem sourceFamily_nonempty (p : PrimitiveInput) (A : FrozenActiveFamily p) :
    Nonempty (SourceFamily p A) := by
  letI := p.upperValues_atomless
  obtain ⟨t,ht,hRt,hmin⟩ := Menus.upper_start_from_source_guard
    p.xi_pos p.xi_lt_one p.lam p.upperSupport p.upper_compact p.upper_nonempty p.R
      p.upper_menu_M1
  obtain ⟨H,hH,hmax⟩ := p.upper_compact.exists_isMaxOn p.upper_nonempty
    continuous_id.continuousOn
  have hbnd : p.upperSupport ⊆ Icc t H := fun v hv => ⟨hmin v hv,hmax hv⟩
  have hsupport : ∀ᵐ v ∂(p.upperValues : Measure ℝ), v ∈ Icc t H :=
    p.upper_supported.mono (fun v hv => hbnd hv)
  have hcap := eventually_capacity_valid p.capacity p.rho_pos p.rho_lt_one p.capacity_limit
  have hupper := eventually_actual_upper_hidden_guard p.upperValues p.h p.rho p.eta
    p.h_pos p.h_le_one p.rho_lower p.rho_lt_one p.eta_pos p.capacity p.capacity_limit
    t p.R H p.R_pos hRt hsupport
  have hlow : ∀ᶠ m : ℕ in atTop,
      0 < (CommonList.iid p.categories (m-1)).prob
        (LowBody.LocalUnderflow (p.capacity m) 0) ∧
      (CommonList.iid p.categories (m-1)).prob (LowBody.BothUnderflow (p.capacity m)) ≤
        (CommonList.iid p.categories (m-1)).prob
          (LowBody.LocalUnderflow (p.capacity m) 0)/4 := by
    have hh := LowBody.eventually_primitive_source_guards p.s p.a p.h p.s_pos
      p.a_pos.le p.h_pos p.mass (Measure.dirac (0:ℝ)) p.capacity p.rho p.eta
      p.rho_pos p.rho_upper p.eta_pos.le p.capacity_limit p.low_rate_gap
    filter_upwards [hh] with m hm
    exact ⟨hm.2.2.1,hm.2.2.2.2.1⟩
  obtain ⟨n,hn⟩ := eventually_atTop.mp (hcap.and (hlow.and hupper))
  exact ⟨{
    start := max A.start n
    start_ge := le_max_left _ _
    t := t
    H := H
    t_mem := ht
    H_mem := hH
    Rt := hRt
    upperSupport_bounds := hbnd
    capacity_valid := fun m hm => (hn m ((le_max_right _ _).trans hm)).1
    low_guards := fun m hm => (hn m ((le_max_right _ _).trans hm)).2.1
    upper_guard := fun m hm => (hn m ((le_max_right _ _).trans hm)).2.2 }⟩

namespace SourceFamily
variable {p : PrimitiveInput} {A : FrozenActiveFamily p} (S : SourceFamily p A)

local instance originalUpperNull : NullSingletonClass (p.upperValues : Measure ℝ) :=
  p.upperValues_atomless

def N (k : ℕ) : ℕ := k+S.start+1
def M (k : ℕ) : ℕ := S.N k+1
def C (k : ℕ) : ℕ := p.capacity (S.M k)

@[simp] theorem M_eq_N_add_one (k : ℕ) : S.M k = S.N k+1 := rfl
@[simp] theorem M_sub_one (k : ℕ) : S.M k-1 = S.N k := by simp only [M,Nat.add_sub_cancel]
theorem start_le_M (k : ℕ) : S.start ≤ S.M k := by dsimp [M,N]; omega
theorem market_ge (k : ℕ) : A.start ≤ S.M k := S.start_ge.trans (S.start_le_M k)
theorem valid (k : ℕ) : 2 ≤ S.M k ∧ 1 ≤ S.C k ∧ S.C k < S.M k :=
  S.capacity_valid _ (S.start_le_M k)
theorem N_tendsto : Tendsto S.N atTop atTop := by
  convert! tendsto_add_atTop_nat (S.start+1) using 1
 theorem M_tendsto : Tendsto S.M atTop atTop := by
  convert! tendsto_add_atTop_nat (S.start+2) using 1
theorem capacity_limit : Tendsto (fun k => (S.C k:ℝ)/(S.M k:ℝ)) atTop (𝓝 p.rho) :=
  p.capacity_limit.comp S.M_tendsto
theorem t_pos : 0 < S.t := p.R_pos.trans S.Rt
theorem H_pos : 0 < S.H := S.t_pos.trans_le (S.upperSupport_bounds S.t_mem).2
theorem upper_supported : ∀ᵐ v ∂(p.upperValues : Measure ℝ), v ∈ Icc S.t S.H :=
  p.upper_supported.mono (fun _ hv => S.upperSupport_bounds hv)

private theorem lowWitness_exists (k : ℕ) :
    ∃ W : LowBody.ActualAtomlessLowLimit (S.N k) p.d p.xi (S.C k)
      p.categories (p.lowValues : Measure p.Low),
      A.low (S.M k) = W.joint.1.map measurable_snd.aemeasurable := by
  have h := A.low_witness (S.M k) (S.market_ge k)
  rw [S.M_sub_one k] at h
  exact h

def lowWitness (k : ℕ) : LowBody.ActualAtomlessLowLimit (S.N k) p.d p.xi
    (S.C k) p.categories (p.lowValues : Measure p.Low) :=
  Classical.choose (S.lowWitness_exists k)

theorem low_eq (k : ℕ) : A.low (S.M k) =
    (S.lowWitness k).joint.1.map measurable_snd.aemeasurable :=
  Classical.choose_spec (S.lowWitness_exists k)

def lowLaw (k : ℕ) : Measure ℝ := p.lowReal (A.low (S.M k))
def activeLaw (k : ℕ) : Measure ℝ := p.bidReal (A.joint (S.M k))
instance lowLaw_probability (k : ℕ) : IsProbabilityMeasure (S.lowLaw k) :=
  p.lowReal_isProbability _
instance activeLaw_probability (k : ℕ) : IsProbabilityMeasure (S.activeLaw k) :=
  p.bidReal_isProbability _

def PL (k : ℕ) : ProbabilityMeasure (ℝ × JointAction 2) :=
  lowJoint (p.lowValues : Measure p.Low) (S.lowWitness k).joint
def PA (k : ℕ) : ProbabilityMeasure (ℝ × JointAction 2) :=
  activeJoint p.L_pos.le (p.activeValues : Measure p.Value) (A.joint (S.M k))
def upperRank (k : ℕ) : ℝ → ℝ :=
  rank (ENNReal.ofReal p.h • (p.upperValues : Measure ℝ)) (S.M k-1) (S.C k) 2
def upperBid (k : ℕ) : ℝ → ℝ := bid (S.upperRank k) S.t p.R
def PH (k : ℕ) : ProbabilityMeasure (ℝ × JointAction 2) :=
  actualUpperJoint p.upperValues p.h p.h_pos p.h_le_one (S.M k) (S.C k)
    (S.valid k).1 (S.valid k).2.1 (S.valid k).2.2 S.t p.R S.H
    p.R_pos S.Rt S.upper_supported
def P (k : ℕ) : ProbabilityMeasure (ℝ × JointAction 2) :=
  populationLaw p.s p.a p.h p.s_pos.le p.a_pos.le p.h_pos.le p.mass
    (S.PL k) (S.PA k) (S.PH k)
def baseGame (k : ℕ) : FiniteGame (S.M k) 2 (S.C k) unitInterval :=
  PopulationGame.game (S.M k) (S.C k) (S.P k) p.eta p.eta_pos.le p.eta_lt_one p.U
def game (k : ℕ) : FiniteGame (S.M k) 2 (S.C k) unitInterval :=
  nativeC5Game (S.M k) (S.C k) (S.P k) p.eta p.eta_pos.le p.eta_lt_one
    p.d p.L p.U p.R p.z (S.lowLaw k)

theorem lowLaw_eq_realBid (k : ℕ) : S.lowLaw k =
    (LowBody.realLowBidLaw (S.lowWitness k).joint.1 : Measure ℝ) := by
  dsimp only [lowLaw,PrimitiveInput.lowReal]
  rw [S.low_eq k]
  change (((S.lowWitness k).joint.1 : Measure (p.Low × p.Low)).map Prod.snd).map
    Subtype.val = _
  rw [Measure.map_map measurable_subtype_coe measurable_snd]
  rfl

theorem PL_value_marginal (k : ℕ) :
    (S.PL k : Measure (ℝ × JointAction 2)).map Prod.fst =
      (p.lowValues : Measure p.Low).map Subtype.val :=
  lowJoint_value_marginal _ _

theorem PL_bid_marginal (k : ℕ) :
    (S.PL k : Measure (ℝ × JointAction 2)).map (fun x => x.2.bid) = S.lowLaw k :=
  (lowJoint_bid_marginal _ _).trans (S.lowLaw_eq_realBid k).symm

theorem actualLowSeed_eq (k : ℕ) : actualLowSeedLaw (S.lowWitness k) = S.lowLaw k :=
  S.PL_bid_marginal k

theorem seed_eq_producer (k : ℕ) :
    (S.game k).seedLaw = volume ∧ S.lowLaw k = p.lowReal (A.low (S.M k)) := ⟨rfl,rfl⟩

theorem PA_value_marginal (k : ℕ) :
    (S.PA k : Measure (ℝ × JointAction 2)).map Prod.fst =
      (p.activeValues : Measure p.Value).map Subtype.val :=
  activeJoint_value_marginal _ _ _

theorem PA_bid_marginal (k : ℕ) :
    (S.PA k : Measure (ℝ × JointAction 2)).map (fun x => x.2.bid) = S.activeLaw k :=
  activeJoint_bid_marginal _ _ _

theorem PL_support (k : ℕ) : ∀ᵐ x ∂(S.PL k : Measure (ℝ × JointAction 2)),
    x.1 ∈ Icc 0 p.d ∧ x.2.bid ∈ Icc 0 p.d ∧ x.2.routeCount=2 := by
  change ∀ᵐ x ∂((S.lowWitness k).joint.1 : Measure (p.Low × p.Low)).map
    (fun x => (x.1.1,lowBroadcast x.2)), _
  apply (measurableEmbedding_lowJointPoint p.d).ae_map_iff.mpr
  exact ae_of_all _ (fun x => ⟨x.1.property,x.2.property,rfl⟩)

theorem PL_positive_le_value (k : ℕ) :
    ∀ᵐ x ∂(S.PL k : Measure (ℝ × JointAction 2)),
      0 < x.1 ∧ 0 < x.2.bid ∧ x.2.bid ≤ x.1 := by
  change ∀ᵐ x ∂((S.lowWitness k).joint.1 : Measure (p.Low × p.Low)).map
    (fun x => (x.1.1,lowBroadcast x.2)), _
  apply (measurableEmbedding_lowJointPoint p.d).ae_map_iff.mpr
  filter_upwards [(S.lowWitness k).value_positive,(S.lowWitness k).bid_positive,
    (S.lowWitness k).bid_le_value] with x hv hb hle
  exact ⟨hv,hb,hle⟩

theorem PA_support (k : ℕ) : ∀ᵐ x ∂(S.PA k : Measure (ℝ × JointAction 2)),
    x.1 ∈ Icc p.vlo p.vhi ∧ x.2.bid ∈ Icc p.L p.U ∧ x.2.routeCount=2 :=
  activeJoint_support _ _ _

theorem PA_source_support (k : ℕ) :
    ∀ᵐ x ∂(S.PA k : Measure (ℝ × JointAction 2)), x.1 ∈ p.activeSupport := by
  apply (ae_map_iff measurable_fst.aemeasurable
    p.active_compact.isClosed.measurableSet).mp
  rw [S.PA_value_marginal k]
  exact (ae_map_iff measurable_subtype_coe.aemeasurable
    p.active_compact.isClosed.measurableSet).mpr p.active_supported

theorem PA_receipt_support (k : ℕ) :
    ∀ᵐ x ∂(S.PA k : Measure (ℝ × JointAction 2)),
      p.d < ((1+p.eta)/2)*x.2.bid ∧ x.2.bid ≤ p.U ∧ x.2.routeCount=2 := by
  filter_upwards [S.PA_support k] with x hx
  have hg : p.d < ((1+p.eta)/2)*p.L := by nlinarith [p.low_receipt]
  have hh := hg.trans_le
    (mul_le_mul_of_nonneg_left hx.2.1.1 (by linarith [p.eta_pos] : 0 ≤ (1+p.eta)/2))
  exact ⟨hh,hx.2.1.2,hx.2.2⟩

theorem PA_kappa_support (k : ℕ) :
    ∀ᵐ x ∂(S.PA k : Measure (ℝ × JointAction 2)),
      p.d < p.kappa*x.2.bid ∧ x.2.routeCount=2 := by
  filter_upwards [S.PA_support k] with x hx
  exact ⟨p.low_receipt.trans_le
    (mul_le_mul_of_nonneg_left hx.2.1.1 p.kappa_pos.le),hx.2.2⟩

theorem lowLaw_supported (k : ℕ) : ∀ᵐ b ∂S.lowLaw k, b ∈ Icc 0 p.d := by
  change ∀ᵐ b ∂(A.low (S.M k) : Measure p.Low).map Subtype.val, _
  apply (ae_map_iff measurable_subtype_coe.aemeasurable measurableSet_Icc).mpr
  exact ae_of_all _ (fun b => b.property)

theorem activeLaw_supported (k : ℕ) : ∀ᵐ b ∂S.activeLaw k, b ∈ Icc p.L p.U := by
  change ∀ᵐ b ∂(((A.joint (S.M k)).1 : Measure (p.Value × p.Bid)).map Prod.snd).map
    Subtype.val, _
  apply (ae_map_iff measurable_subtype_coe.aemeasurable measurableSet_Icc).mpr
  exact ae_of_all _ (fun b => b.property)

theorem lowLaw_atomless (k : ℕ) : NullSingletonClass (S.lowLaw k) := by
  rw [S.lowLaw_eq_realBid k]
  exact (S.lowWitness k).real_atomless

theorem activeLaw_atomless (k : ℕ) : NullSingletonClass (S.activeLaw k) := by
  letI := A.atomless (S.M k) (S.market_ge k)
  change NullSingletonClass
    (((A.joint (S.M k)).1.map measurable_snd.aemeasurable : Measure p.Bid).map Subtype.val)
  constructor
  intro b
  rw [Measure.map_apply measurable_subtype_coe (measurableSet_singleton b)]
  apply Set.Countable.measure_zero
  apply Set.Subsingleton.countable
  intro x hx y hy
  exact Subtype.ext (hx.trans hy.symm)

theorem lowLaw_singletons (k : ℕ) (b : ℝ) : S.lowLaw k {b}=0 :=
  (S.lowLaw_atomless k).measure_singleton b

theorem activeLaw_singletons (k : ℕ) (b : ℝ) : S.activeLaw k {b}=0 :=
  (S.activeLaw_atomless k).measure_singleton b

theorem jointBidLaw_low (k : ℕ) : (jointBidLaw (S.PL k) : Measure ℝ)=S.lowLaw k :=
  S.PL_bid_marginal k

theorem jointBidLaw_active (k : ℕ) : (jointBidLaw (S.PA k) : Measure ℝ)=S.activeLaw k :=
  S.PA_bid_marginal k

theorem PL_bid_singleton (k : ℕ) (b : ℝ) :
    (S.PL k : Measure (ℝ × JointAction 2)) {x | x.2.bid=b}=0 := by
  letI := S.lowLaw_atomless k
  have hh := measure_singleton (μ := S.lowLaw k) b
  rw [← S.PL_bid_marginal k] at hh
  have hm : Measurable (fun x : ℝ × JointAction 2 => x.2.bid) := (measurable_bid 2).comp measurable_snd
  rw [Measure.map_apply hm (measurableSet_singleton b)] at hh
  exact hh

theorem PA_bid_singleton (k : ℕ) (b : ℝ) :
    (S.PA k : Measure (ℝ × JointAction 2)) {x | x.2.bid=b}=0 := by
  letI := S.activeLaw_atomless k
  have hh := measure_singleton (μ := S.activeLaw k) b
  rw [← S.PA_bid_marginal k] at hh
  have hm : Measurable (fun x : ℝ × JointAction 2 => x.2.bid) := (measurable_bid 2).comp measurable_snd
  rw [Measure.map_apply hm (measurableSet_singleton b)] at hh
  exact hh

theorem upperBid_measurable (k : ℕ) : Measurable (S.upperBid k) :=
  actualUpperBid_measurable p.upperValues p.h p.h_pos p.h_le_one (S.M k) (S.C k)
    (S.valid k).1 (S.valid k).2.1 (S.valid k).2.2 S.t p.R S.H
    p.R_pos S.Rt S.upper_supported

theorem upperBid_bounds (k : ℕ) (v : ℝ) (hv : S.t ≤ v) :
    p.R ≤ S.upperBid k v ∧ S.upperBid k v ≤ v :=
  (actualUpperEnvelope p.upperValues p.h p.h_pos p.h_le_one (S.M k) (S.C k)
    (S.valid k).1 (S.valid k).2.1 (S.valid k).2.2 S.t p.R S.H
    p.R_pos S.Rt S.upper_supported).bid_bounds v hv

theorem PH_spec (k : ℕ) :
    (S.PH k : Measure (ℝ × JointAction 2)).map Prod.fst = (p.upperValues : Measure ℝ) ∧
    (S.PH k : Measure (ℝ × JointAction 2)).map (fun x => x.2.bid) =
      (p.upperValues : Measure ℝ).map (S.upperBid k) ∧
    (∀ᵐ x ∂(S.PH k : Measure (ℝ × JointAction 2)),
      x.1 ∈ Icc S.t S.H ∧ x.2=upperAction (S.upperBid k) x.1 ∧
        p.R ≤ x.2.bid ∧ x.2.routeCount=1) ∧
    (∀ b : ℝ, (S.PH k : Measure (ℝ × JointAction 2)) {x | x.2.bid=b}=0) :=
  actualUpperJoint_spec p.upperValues p.h p.h_pos p.h_le_one (S.M k) (S.C k)
    (S.valid k).1 (S.valid k).2.1 (S.valid k).2.2 S.t p.R S.H
    p.R_pos S.Rt S.upper_supported

theorem PH_support (k : ℕ) : ∀ᵐ x ∂(S.PH k : Measure (ℝ × JointAction 2)),
    p.R ≤ x.2.bid ∧ x.2.routeCount=1 :=
  (S.PH_spec k).2.2.1.mono (fun _ hx => hx.2.2)

theorem PH_source_support (k : ℕ) :
    ∀ᵐ x ∂(S.PH k : Measure (ℝ × JointAction 2)), x.1 ∈ p.upperSupport := by
  apply (ae_map_iff measurable_fst.aemeasurable
    p.upper_compact.isClosed.measurableSet).mp
  rw [(S.PH_spec k).1]
  exact p.upper_supported

theorem active_source_support (k : ℕ) :
    ∀ᵐ x ∂(S.PA k : Measure (ℝ × JointAction 2)), x.1 ∈ p.activeSupport :=
  S.PA_source_support k

theorem upper_source_support (k : ℕ) :
    ∀ᵐ x ∂(S.PH k : Measure (ℝ × JointAction 2)), x.1 ∈ p.upperSupport :=
  S.PH_source_support k

theorem low_source_support (k : ℕ) :
    ∀ᵐ x ∂(S.PL k : Measure (ℝ × JointAction 2)), 0 < x.1 ∧ x.1 ≤ p.d := by
  filter_upwards [S.PL_positive_le_value k,S.PL_support k] with x hx hs
  exact ⟨hx.1,hs.1.2⟩

theorem PH_graph (k : ℕ) : ∀ᵐ x ∂(S.PH k : Measure (ℝ × JointAction 2)),
    x.2=upperAction (S.upperBid k) x.1 :=
  (S.PH_spec k).2.2.1.mono (fun _ hx => hx.2.1)

theorem PH_bid_singleton (k : ℕ) (b : ℝ) :
    (S.PH k : Measure (ℝ × JointAction 2)) {x | x.2.bid=b}=0 :=
  (S.PH_spec k).2.2.2 b

theorem original_F (k : ℕ) : (S.game k).F = p.originalValues := by
  change (populationJoint p.s p.a p.h (S.PL k) (S.PA k) (S.PH k)).map Prod.fst = _
  exact original_population_marginal p.s p.a p.h (S.PL k) (S.PA k) (S.PH k)
    ((p.lowValues : Measure p.Low).map Subtype.val)
    ((p.activeValues : Measure p.Value).map Subtype.val) p.upperValues
    (S.PL_value_marginal k) (S.PA_value_marginal k) (S.PH_spec k).1

theorem joint (k : ℕ) : (S.game k).F ⊗ₘ (S.game k).σ =
    (S.P k : Measure (ℝ × JointAction 2)) :=
  nativeC5Game_joint_law _ _ _ _ _ _ _ _ _ _ _ _

theorem joint_original_components (k : ℕ) : (S.game k).F ⊗ₘ (S.game k).σ =
    populationJoint p.s p.a p.h (S.PL k) (S.PA k) (S.PH k) := S.joint k

theorem game_eq_closed (k : ℕ) : S.game k =
    ClosedPolicy.nativeGame
      (FullContext.contextPolicy p.xi_pos p.xi_lt_one p.d p.L p.U p.z (S.C k) (S.lowLaw k))
      (S.baseGame k) p.R := rfl

def price (k : ℕ) : ℝ := p.h0/reciprocalMean (S.activeLaw k)

theorem price_limit : Tendsto S.price atTop (𝓝 p.lam) :=
  A.price_limit.comp S.M_tendsto

theorem P_shape (k : ℕ) : ∀ᵐ x ∂(S.P k : Measure (ℝ × JointAction 2)),
    (x.2.bid < p.R ∧ x.2.routeCount=2) ∨ (p.R ≤ x.2.bid ∧ x.2.routeCount=1) := by
  apply original_population_mixture_ae p.s p.a p.h (S.PL k) (S.PA k) (S.PH k)
  · exact (S.PL_support k).mono (fun x hx =>
      Or.inl ⟨hx.2.1.2.trans_lt (p.d_lt_L.trans (p.L_lt_U.trans p.upper_floor)),hx.2.2⟩)
  · exact (S.PA_support k).mono (fun x hx => Or.inl ⟨hx.2.1.2.trans_lt p.upper_floor,hx.2.2⟩)
  · exact (S.PH_support k).mono (fun _ hx => Or.inr hx)

theorem profile_support (k : ℕ) : ∀ᵐ x ∂userProfileLaw (S.game k),
    x ∈ closedProfiles (S.M k) p.R :=
  nativeC5Game_profile_support _ _ _ _ _ _ _ _ _ _ _ _ (S.P_shape k)

theorem context_facts (k : ℕ) :
    (∀ᵐ x ∂userProfileLaw (S.baseGame k), x ∈ closedProfiles (S.M k) p.R) ∧
    (∀ᵐ x ∂(S.baseGame k).F ⊗ₘ (S.baseGame k).σ, x.2.bid ≤ p.U ∨ p.R ≤ x.2.bid) ∧
    (userLaw (S.baseGame k)).map (physicalRow p.d p.U) =
      physicalRivalLaw p.s p.a p.h (S.lowLaw k) (S.activeLaw k) := by
  have hh := native_population_context_facts (m := S.M k) (c := S.C k)
    p.d_lt_L p.L_lt_U.le p.upper_floor p.s p.a p.h p.s_pos.le p.a_pos.le p.h_pos.le p.mass
    (S.PL k) (S.PA k) (S.PH k)
    ((S.PL_support k).mono (fun _ hx => ⟨hx.2.1.2,hx.2.2⟩))
    ((S.PA_support k).mono (fun _ hx => hx.2)) (S.PH_support k)
    p.eta p.eta_pos.le p.eta_lt_one
  simpa only [jointBidLaw_coe,S.PL_bid_marginal k,S.PA_bid_marginal k, baseGame, P] using hh

theorem P_bid_singleton (k : ℕ) (b : ℝ) :
    (S.P k : Measure (ℝ × JointAction 2)) {x | x.2.bid=b}=0 := by
  change populationJoint p.s p.a p.h (S.PL k) (S.PA k) (S.PH k) {x | x.2.bid=b}=0
  simp only [populationJoint,Measure.add_apply,Measure.smul_apply,smul_eq_mul,
    S.PL_bid_singleton k b,S.PA_bid_singleton k b,S.PH_bid_singleton k b,mul_zero,add_zero]

theorem P_bid_atomless (k : ℕ) : NullSingletonClass
    ((S.P k : Measure (ℝ × JointAction 2)).map (fun x => x.2.bid)) := by
  constructor
  intro b
  have hm : Measurable (fun x : ℝ × JointAction 2 => x.2.bid) := (measurable_bid 2).comp measurable_snd
  rw [Measure.map_apply hm (measurableSet_singleton b)]
  exact S.P_bid_singleton k b

theorem low_guards_at (k : ℕ) :
    0 < (CommonList.iid p.categories (S.N k)).prob (LowBody.LocalUnderflow (S.C k) 0) ∧
    (CommonList.iid p.categories (S.N k)).prob (LowBody.BothUnderflow (S.C k)) ≤
      (CommonList.iid p.categories (S.N k)).prob (LowBody.LocalUnderflow (S.C k) 0)/4 := by
  have h := S.low_guards (S.M k) (S.start_le_M k)
  rw [S.M_sub_one k] at h
  exact h

theorem lowUsersOptimal (k : ℕ) (i : Fin (S.M k)) :
    ∀ᵐ x ∂(S.PL k : Measure (ℝ × JointAction 2)),
      (problem (S.game k) i).BestResponse x.1 x.2 ∧
      ∀ act : JointAction 2, act.routeCount=1 →
        (problem (S.game k) i).payoff x.1 act < (problem (S.game k) i).payoff x.1 x.2 := by
  have hh := nativeC5LowUsersOptimal (N := S.N k) (c := S.C k) (d := p.d)
    (L := p.L) (U := p.U) (R := p.R) (eta := p.eta) (z := p.z) p.d_nonneg (p.d_lt_L.le.trans p.L_lt_U.le)
    p.upper_floor p.low_receipt p.s p.a p.h p.s_pos.le p.a_pos.le p.h_pos.le p.mass
    (Measure.dirac (0:ℝ)) (p.lowValues : Measure p.Low) p.eta_pos.le p.eta_lt_one
    (S.lowWitness k) (S.PA k) (S.PH k) (S.PA_receipt_support k) (S.PH_support k)
    (S.low_guards_at k).1 (S.low_guards_at k).2 i
  dsimp only at hh
  have hg : nativeC5Game (S.M k) (S.C k) (S.P k) p.eta p.eta_pos.le p.eta_lt_one
      p.d p.L p.U p.R p.z (actualLowSeedLaw (S.lowWitness k)) = S.game k := by
    rw [S.actualLowSeed_eq k]
    rfl
  have hh' : ∀ᵐ x ∂(S.PL k : Measure (ℝ × JointAction 2)),
      (problem (nativeC5Game (S.M k) (S.C k) (S.P k) p.eta p.eta_pos.le p.eta_lt_one
        p.d p.L p.U p.R p.z (actualLowSeedLaw (S.lowWitness k))) i).BestResponse x.1 x.2 ∧
      ∀ act : JointAction 2, act.routeCount=1 →
        (problem (nativeC5Game (S.M k) (S.C k) (S.P k) p.eta p.eta_pos.le p.eta_lt_one
          p.d p.L p.U p.R p.z (actualLowSeedLaw (S.lowWitness k))) i).payoff x.1 act <
        (problem (nativeC5Game (S.M k) (S.C k) (S.P k) p.eta p.eta_pos.le p.eta_lt_one
          p.d p.L p.U p.R p.z (actualLowSeedLaw (S.lowWitness k))) i).payoff x.1 x.2 := by
    convert! hh using 1
  rw [hg] at hh'
  exact hh'

theorem upperPackage (k : ℕ) :
    NativeUpperPackage (S.game k) (S.PH k) (S.upperRank k) (S.upperBid k) S.t p.R S.H :=
  closed_actual_upper_package (S.M k) (S.C k) (S.valid k).1 (S.valid k).2.1 (S.valid k).2.2
    p.U p.s p.a p.h p.U_pos.le p.s_pos.le p.a_pos.le p.h_pos p.h_le_one p.mass
    (S.PL k) (S.PA k) p.upperValues
    ((S.PL_support k).mono (fun _ hx => hx.2.1.2.trans (p.d_lt_L.le.trans p.L_lt_U.le)))
    ((S.PA_support k).mono (fun _ hx => hx.2.1.2)) p.eta p.eta_pos.le p.eta_lt_one
    S.t p.R S.H p.R_pos S.Rt p.upper_floor S.upper_supported
    (nativeC5Context (S.M k) (S.C k) p.eta p.eta_pos.le p.eta_lt_one
      p.d p.L p.U p.z (S.lowLaw k))
    (S.upper_guard (S.M k) (S.start_le_M k))

theorem upper_limits :
    Tendsto (fun k => S.upperRank k S.t) atTop (𝓝 1) ∧
    Tendsto (fun k => error (S.upperRank k) S.t p.R) atTop (𝓝 0) := by
  obtain ⟨hq,hE⟩ := upper_source_error_limits p.upperValues p.h p.rho p.h_pos p.h_le_one
    p.rho_lower p.rho_lt_one p.capacity p.capacity_limit S.t p.R S.H S.Rt.le S.upper_supported
  exact ⟨hq.comp S.M_tendsto,hE.comp S.M_tendsto⟩

theorem proposerRational (k : ℕ) :
    ∀ j, ProposerRationalAtFeasibleLists (S.game k) j :=
  nativeC5RationalAtFeasibleLists (S.M k) (S.C k) (S.P k) p.eta p.eta_pos.le p.eta_lt_one
    p.d p.L p.U p.R p.z p.R_pos (S.lowLaw k) (S.P_shape k)

end SourceFamily
end FCAppendix.Affine.Hybrid.Native02
