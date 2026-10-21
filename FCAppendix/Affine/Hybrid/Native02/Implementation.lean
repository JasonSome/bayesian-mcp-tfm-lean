import FCAppendix.Affine.Hybrid.Native02.SourceGlobalIC
import FCAppendix.Affine.Hybrid.Native02.SourceAggregates
import FCAppendix.Affine.Hybrid.Native02.FrozenActiveAdapter

noncomputable section
namespace FCAppendix.Affine.Hybrid.Native02
open MeasureTheory ProbabilityTheory Set Filter Topology Game Bayes

structure NativeFamilyData (p : PrimitiveInput) where
  active : FrozenActiveFamily p
  source : SourceFamily p active
  shift : ℕ
  valueSet : Set ℝ
  measurable_valueSet : MeasurableSet valueSet
  full_valueSet : ∀ᵐv ∂p.originalValues,v∈ valueSet

namespace NativeFamilyData
variable {p : PrimitiveInput} (D : NativeFamilyData p)

def index (k : ℕ) : ℕ := k+D.shift
def M (k : ℕ) : ℕ := D.source.M (D.index k)
def C (k : ℕ) : ℕ := p.capacity (D.M k)
def offset : ℕ := D.shift+D.source.start+2

theorem M_eq (k : ℕ) : D.M k=k+D.offset := by
  dsimp [M,index,offset,SourceFamily.M,SourceFamily.N]
  omega
theorem index_tendsto : Tendsto D.index atTop atTop := tendsto_add_atTop_nat D.shift
theorem M_tendsto : Tendsto D.M atTop atTop := D.source.M_tendsto.comp D.index_tendsto
theorem capacity_limit : Tendsto (fun k=>(D.C k:ℝ)/(D.M k:ℝ)) atTop (𝓝 p.rho) :=
  p.capacity_limit.comp D.M_tendsto
theorem market_valid (k : ℕ) : 2≤ D.M k ∧ 1≤ D.C k ∧ D.C k< D.M k :=
  D.source.valid (D.index k)

def baseGame (k : ℕ) : FiniteGame (D.M k) 2 (D.C k) unitInterval :=
  D.source.game (D.index k)

def nullAction (k : ℕ) : ℝ→ JointAction 2 :=
  sourceNullAction p.value_order p.L_pos.le p.d D.source.t D.active.targetBid
    (D.source.upperBid (D.index k))

theorem measurable_nullAction (k : ℕ) : Measurable (D.nullAction k) :=
  measurable_sourceNullAction p.value_order p.L_pos.le p.d D.source.t
    D.active.targetBid D.active.measurable_targetBid
    (D.source.upperBid (D.index k)) (D.source.upperBid_measurable (D.index k))

def game (k : ℕ) : FiniteGame (D.M k) 2 (D.C k) unitInterval :=
  nullTypeGame (D.baseGame k) D.valueSet D.measurable_valueSet
    (D.nullAction k) (D.measurable_nullAction k)

theorem base_original_F (k : ℕ) : (D.baseGame k).F=p.originalValues :=
  D.source.original_F (D.index k)
theorem full_base (k : ℕ) : ∀ᵐv ∂(D.baseGame k).F,v∈ D.valueSet := by
  rw [D.base_original_F]
  exact D.full_valueSet
theorem original_F (k : ℕ) : (D.game k).F=p.originalValues := D.base_original_F k

def posterior (k : ℕ) : PosteriorSystem (D.game k) :=
  nullTypePosterior (D.baseGame k) (D.source.posterior (D.index k))
    D.valueSet D.measurable_valueSet (D.full_base k)
    (D.nullAction k) (D.measurable_nullAction k)

theorem original_tariffs_seed (k : ℕ) :
    (D.game k).g=0 ∧
    (D.game k).A=Schedule.affine 2 p.eta p.eta_pos.le p.eta_lt_one.le ∧
    (D.game k).G=Schedule.once 2 ∧ (D.game k).seedLaw=volume :=
  ⟨rfl,rfl,rfl,rfl⟩

theorem joint_original (k : ℕ) :
    (D.game k).F⊗ₘ(D.game k).σ=
      populationJoint p.s p.a p.h
        (D.source.PL (D.index k)) (D.source.PA (D.index k)) (D.source.PH (D.index k)) := by
  rw [game,nullTypeGame_joint_law _ _ _ (D.full_base k)]
  exact D.source.joint_original_components (D.index k)

theorem bid_atomless (k : ℕ) :
    NullSingletonClass (((D.game k).F⊗ₘ(D.game k).σ).map (fun x=> x.2.bid)) := by
  rw [game,nullTypeGame_joint_law _ _ _ (D.full_base k)]
  change NullSingletonClass (((D.source.game (D.index k)).F⊗ₘ
    (D.source.game (D.index k)).σ).map (fun x=> x.2.bid))
  rw [D.source.joint]
  exact D.source.P_bid_atomless (D.index k)

theorem strategy_inside (k : ℕ) (v : ℝ) (hv : v∈ D.valueSet) :
    (D.game k).σ v=(D.baseGame k).σ v := by
  simp only [game,nullTypeGame,Kernel.piecewise_apply,if_pos hv]

theorem raw_outcome (k : ℕ) (i : Fin (D.M k)) (a : JointAction 2) :
    (problem (D.game k) i).outcome a=(problem (D.baseGame k) i).outcome a :=
  nullTypeGame_outcome _ _ _ (D.full_base k) _ _ i a

theorem raw_payoff (k : ℕ) (i : Fin (D.M k)) (v : ℝ) (a : JointAction 2) :
    (problem (D.game k) i).payoff v a=(problem (D.baseGame k) i).payoff v a :=
  nullTypeGame_payoff _ _ _ (D.full_base k) _ _ i v a

theorem proposer_all_lists_seeds (k : ℕ) : ∀ j X,FeasibleObservedList j X→∀ s,
    Finite.Optimal (D.C k)
      (beliefReceipts (D.game k).A
        (posteriorCountBelief (D.game k) (D.posterior k) j X) X)
      ((D.game k).policy j X s).val := by
  intro j X hX s
  change Finite.Optimal (D.C k)
    (beliefReceipts (D.baseGame k).A
      (posteriorCountBelief (D.baseGame k) (D.source.posterior (D.index k)) j X) X)
    ((D.baseGame k).policy j X s).val
  exact D.source.proposer_all_lists_seeds (D.index k) j X hX s

theorem posterior_optimal (k : ℕ) : PosteriorProposerOptimalAE (D.game k) (D.posterior k) :=
  fun j X hX=> ae_of_all _ (D.proposer_all_lists_seeds k j X hX)

theorem users_optimal_of_base (h : ∀ k,UsersOptimal (D.baseGame k)) :
    ∀ k,UsersOptimal (D.game k) := fun k=>
  nullTypeGame_users_optimal _ _ _ (D.full_base k) _ _ (h k)

theorem low_strict (k : ℕ) (i : Fin (D.M k)) :
    ∀ᵐx ∂(D.source.PL (D.index k) : Measure (ℝ×JointAction 2)),
      (problem (D.game k) i).BestResponse x.1 x.2 ∧
      ∀ a : JointAction 2,a.routeCount=1→
        (problem (D.game k) i).payoff x.1 a<(problem (D.game k) i).payoff x.1 x.2 := by
  filter_upwards [D.source.lowUsersOptimal (D.index k) i] with x hx
  constructor
  · intro a
    simp only [D.raw_payoff]
    convert! hx.1 a using 1
  · intro a ha
    simp only [D.raw_payoff]
    convert! hx.2 a ha using 1

theorem actual_filling_load_limit :
    Tendsto (fun k=> finiteLoad (D.game k)) atTop (𝓝 (2*p.rho)) := by
  have he (k : ℕ) : finiteLoad (D.game k)=finiteLoad (D.source.game (D.index k)) :=
    nullTypeGame_finiteLoad _ _ _ (D.full_base k) _ _
  simp only [he]
  exact D.source.actual_load_limit.comp D.index_tendsto

end NativeFamilyData

structure NativeImplementation (p : PrimitiveInput) extends NativeFamilyData p where
  users_optimal : ∀ k,UsersOptimal (toNativeFamilyData.game k)
  common_bands : ∀ v∈ valueSet,∀ k,∀ᵐa ∂(toNativeFamilyData.game k).σ v,
    OriginalBandSupport p.d p.vlo p.vhi source.t p.L p.U p.R (v,a)
  common_supported_graph : ∀ v∈ valueSet,v∈ Icc p.vlo p.vhi→∀ eps>0,∀ᶠk in atTop,
    ∀ᵐa ∂(toNativeFamilyData.game k).σ v,|a.bid-active.targetReal v|< eps
  common_all_actions : ∀ v∈ valueSet,∀ k,∀ᵐa ∂(toNativeFamilyData.game k).σ v,
    ∀ i : Fin (toNativeFamilyData.M k),∀ dev : JointAction 2,
      (problem (toNativeFamilyData.game k) i).payoff v dev≤
        (problem (toNativeFamilyData.game k) i).payoff v a
  low_count_limit : ∀ v∈ Icc (0:ℝ) p.d,∀ i : ∀ k,Fin (toNativeFamilyData.M k),∀ r,
    Tendsto (fun k=>(typeOutcome (toNativeFamilyData.game k) (i k) v).mass r)
      atTop (𝓝 ((FiniteLaw.dirac (0:Fin 3)).mass r))
  active_count_limit : ∀ v : p.Value,∀ i : ∀ k,Fin (toNativeFamilyData.M k),∀ r,
    Tendsto (fun k=>(typeOutcome (toNativeFamilyData.game k) (i k) v.1).mass r)
      atTop (𝓝 ((p.activeCount v).mass r))
  upper_count_limit : ∀ v,p.vhi< v→∀ i : ∀ k,Fin (toNativeFamilyData.M k),∀ r,
    Tendsto (fun k=>(typeOutcome (toNativeFamilyData.game k) (i k) v).mass r)
      atTop (𝓝 ((FiniteLaw.dirac (1:Fin 3)).mass r))
  coverage_limit : Tendsto (fun k=> finiteCoverage (toNativeFamilyData.game k))
    atTop (𝓝 p.coverage)
  load_limit : Tendsto (fun k=> finiteLoad (toNativeFamilyData.game k))
    atTop (𝓝 (2*p.rho))
  duplicates_limit : Tendsto (fun k=> finiteLoad (toNativeFamilyData.game k)-
    finiteCoverage (toNativeFamilyData.game k)) atTop (𝓝 p.duplicates)
  multiplicity_limit : Tendsto (fun k=> finiteMultiplicity (toNativeFamilyData.game k))
    atTop (𝓝 (2*p.rho/p.coverage))

theorem native_affine_implementation_of_active_family (p : PrimitiveInput)
    (A : FrozenActiveFamily p) : Nonempty (NativeImplementation p) := by
  classical
  obtain ⟨S⟩:=sourceFamily_nonempty p A
  obtain ⟨n,hn⟩:=eventually_atTop.mp S.eventually_usersOptimal
  let T : ℕ→ℕ:=fun k=> k+n
  have hT : Tendsto T atTop atTop := tendsto_add_atTop_nat n
  let M : ℕ→ℕ:=fun k=> S.M (T k)
  let C : ℕ→ℕ:=fun k=> S.C (T k)
  let G : ∀ k,FiniteGame (M k) 2 (C k) unitInterval:=fun k=> S.game (T k)
  have hIC (k : ℕ) : UsersOptimal (G k) := hn (T k) (by dsimp [T];omega)
  have hF (k : ℕ) : (G k).F=p.originalValues := S.original_F (T k)
  have hb (k : ℕ) : ∀ᵐx ∂(G k).F⊗ₘ(G k).σ,
      OriginalBandSupport p.d p.vlo p.vhi S.t p.L p.U p.R x :=
    S.original_band_support (T k)
  have hg : ∀ eps>0,∀ᶠk in atTop,∀ᵐx ∂(G k).F⊗ₘ(G k).σ,
      x.1∈ Icc p.vlo p.vhi→|x.2.bid-A.targetReal x.1|< eps :=
    fun eps heps=> hT.eventually (S.original_supported_graph eps heps)
  obtain ⟨V,hV,hfull,hcommon⟩:=source_common_conull_set p A G p.originalValues
    hF S.t hIC hb hg
  let D : NativeFamilyData p:={
    active:=A,source:=S,shift:=n,valueSet:=V,
    measurable_valueSet:=hV,full_valueSet:=hfull }
  have hbase (k : ℕ) : D.baseGame k=G k := rfl
  have husers : ∀ k,UsersOptimal (D.game k) :=
    D.users_optimal_of_base (fun k=> hIC k)
  have hbands : ∀ v∈ D.valueSet,∀ k,∀ᵐa ∂(D.game k).σ v,
      OriginalBandSupport p.d p.vlo p.vhi S.t p.L p.U p.R (v,a) := by
    intro v hv k
    rw [D.strategy_inside k v hv]
    exact (hcommon v hv).1 k
  have hgraph : ∀ v∈ D.valueSet,v∈ Icc p.vlo p.vhi→∀ eps>0,∀ᶠk in atTop,
      ∀ᵐa ∂(D.game k).σ v,|a.bid-A.targetReal v|< eps := by
    intro v hv hvb eps heps
    filter_upwards [(hcommon v hv).2.1 hvb eps heps] with k hk
    rw [D.strategy_inside k v hv]
    exact hk
  have hall : ∀ v∈ D.valueSet,∀ k,∀ᵐa ∂(D.game k).σ v,
      ∀ i : Fin (D.M k),∀ dev : JointAction 2,
        (problem (D.game k) i).payoff v dev≤(problem (D.game k) i).payoff v a := by
    intro v hv k
    rw [D.strategy_inside k v hv]
    filter_upwards [(hcommon v hv).2.2 k] with a ha
    intro i dev
    simp only [D.raw_payoff, hbase]
    convert! ha i dev using 1
  obtain ⟨lowError,hlow0,hlow,hrawLow⟩:=S.exists_low_service_error
  have hcounts:=source_null_completed_count_limits p A G p.originalValues hF S.t
    S.vhi_lt_t V hV hfull (fun v hv=>(hcommon v hv).1)
    (fun v hv=>(hcommon v hv).2.1)
    (fun k=> lowError (T k)) (hlow.comp hT) (hT.eventually hrawLow)
    (fun eps heps=> hT.eventually (S.rawActiveCountLimit eps heps))
    (fun k=> S.upperRank (T k) S.t) (S.upper_limits.1.comp hT)
    (fun k i a ha hk=> S.upper_raw_count_floor (T k) i a ha hk)
    (fun k=> S.upperBid (T k)) (fun k=> S.upperBid_measurable (T k))
    (fun k v hv=> S.upperBid_floor (T k) v hv)

  dsimp only at hcounts
  have hlowFinal : ∀ v∈ Icc (0:ℝ) p.d,∀ i : ∀ k,Fin (D.M k),∀ r,
      Tendsto (fun k=>(typeOutcome (D.game k) (i k) v).mass r)
        atTop (𝓝 ((FiniteLaw.dirac (0:Fin 3)).mass r)) := hcounts.1
  have hactiveFinal : ∀ v : p.Value,∀ i : ∀ k,Fin (D.M k),∀ r,
      Tendsto (fun k=>(typeOutcome (D.game k) (i k) v.1).mass r)
        atTop (𝓝 ((p.activeCount v).mass r)) := hcounts.2.1
  have hupperFinal : ∀ v,p.vhi< v→∀ i : ∀ k,Fin (D.M k),∀ r,
      Tendsto (fun k=>(typeOutcome (D.game k) (i k) v).mass r)
        atTop (𝓝 ((FiniteLaw.dirac (1:Fin 3)).mass r)) := hcounts.2.2
  obtain ⟨hQ,hload,hdup,hmult⟩:=actual_source_aggregate_limits p A D.game
    (fun k=> lt_of_lt_of_le (by norm_num : 0<2) (D.market_valid k).1)
    D.original_F S.t (fun v hv=>(S.upperSupport_bounds hv).1)
    hlowFinal hactiveFinal (fun v hv=> hupperFinal v (S.vhi_lt_t.trans_le hv))
  refine ⟨{
    toNativeFamilyData:=D,
    users_optimal:=husers,
    common_bands:=hbands,
    common_supported_graph:=hgraph,
    common_all_actions:=hall,
    low_count_limit:=hlowFinal,
    active_count_limit:=hactiveFinal,
    upper_count_limit:=hupperFinal,
    coverage_limit:=hQ,
    load_limit:=D.actual_filling_load_limit,
    duplicates_limit:=hdup,
    multiplicity_limit:=hmult }⟩

theorem native_affine_implementation (produce : ActiveProducer) (p : PrimitiveInput) :
    Nonempty (NativeImplementation p) := by
  obtain ⟨A⟩:=produce p
  exact native_affine_implementation_of_active_family p A

theorem eventually_affine_implementation (produce : ActiveProducer) (p : PrimitiveInput) :
    Nonempty (NativeImplementation p) := native_affine_implementation produce p

theorem nativeC5UsersOptimal {p : PrimitiveInput} (I : NativeImplementation p) (k : ℕ) :
    UsersOptimal (I.toNativeFamilyData.game k) := I.users_optimal k

namespace NativeImplementation
variable {p : PrimitiveInput} (I : NativeImplementation p)

theorem equilibrium (k : ℕ) : IsAEEquilibrium (I.toNativeFamilyData.game k) :=
  posterior_isAEEquilibrium _ (I.users_optimal k)
    (I.toNativeFamilyData.posterior k) (I.toNativeFamilyData.posterior_optimal k)

theorem upper_count_limit_on_original_band (vH : ℝ) (hH : p.vhi< vH)
    (v : ℝ) (hv : vH≤ v) (i : ∀ k,Fin (I.toNativeFamilyData.M k)) (r : Fin 3) :
    Tendsto (fun k=>(typeOutcome (I.toNativeFamilyData.game k) (i k) v).mass r)
      atTop (𝓝 ((FiniteLaw.dirac (1:Fin 3)).mass r)) :=
  I.upper_count_limit v (hH.trans_le hv) i r

theorem every_large_market : ∀ m≥ I.toNativeFamilyData.offset,
    ∃G : FiniteGame m 2 (p.capacity m) unitInterval,∃B : PosteriorSystem G,
      G.F=p.originalValues ∧ G.g=0 ∧
      G.A=Schedule.affine 2 p.eta p.eta_pos.le p.eta_lt_one.le ∧
      G.G=Schedule.once 2 ∧ G.seedLaw=volume ∧
      UsersOptimal G ∧ IsAEEquilibrium G ∧
      (∀ j X,FeasibleObservedList j X→∀ s,
        Finite.Optimal (p.capacity m)
          (beliefReceipts G.A (posteriorCountBelief G B j X) X) (G.policy j X s).val) := by
  intro m hm
  let k:=m-I.toNativeFamilyData.offset
  have he : I.toNativeFamilyData.M k=m := by
    rw [I.toNativeFamilyData.M_eq]
    dsimp only [k]
    omega
  have hout : ∃G : FiniteGame (I.toNativeFamilyData.M k) 2
      (p.capacity (I.toNativeFamilyData.M k)) unitInterval,∃B : PosteriorSystem G,
      G.F=p.originalValues ∧ G.g=0 ∧
      G.A=Schedule.affine 2 p.eta p.eta_pos.le p.eta_lt_one.le ∧
      G.G=Schedule.once 2 ∧ G.seedLaw=volume ∧
      UsersOptimal G ∧ IsAEEquilibrium G ∧
      (∀ j X,FeasibleObservedList j X→∀ s,
        Finite.Optimal (p.capacity (I.toNativeFamilyData.M k))
          (beliefReceipts G.A (posteriorCountBelief G B j X) X) (G.policy j X s).val) := by
    have ht:=I.toNativeFamilyData.original_tariffs_seed k
    exact ⟨I.toNativeFamilyData.game k,I.toNativeFamilyData.posterior k,
      I.toNativeFamilyData.original_F k,ht.1,ht.2.1,ht.2.2.1,ht.2.2.2,
      I.users_optimal k,I.equilibrium k,I.toNativeFamilyData.proposer_all_lists_seeds k⟩
  rw [←he]
  exact hout

end NativeImplementation
end FCAppendix.Affine.Hybrid.Native02
