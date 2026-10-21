import FCAppendix.Affine.Tail04.LowFixedValueVersions
import FCAppendix.Affine.Tail04.ZeroNativeBindings
import FCAppendix.Affine.Tail04.OriginalMovingLow
import FCAppendix.Affine.Tail04.MarketLimits

noncomputable section
namespace FCAppendix.Affine.Tail04.SourceLowCountLaws
open MeasureTheory ProbabilityTheory Set Classical Game Bayes Filter Topology
open Existence.Distributional OriginalValues OriginalPopulation LowBody
open FiniteTailNoisyGame SourceTailNoisyFixedPoint NativeZeroNoiseSource ZeroNativeBindings
open NativeLowCountBounds LowFixedValueVersions
open scoped BigOperators

section Finite
variable (D : Data) (P : ValueParameters) (t : ℝ) (ht : P.M< t)
  (hdR : P.d0< D.R) (H : ℝ) (hUH : D.U< H) (N : ℕ)
  (L : ActualAtomlessLowLimit N P.d0 D.ξ D.c
    (NativeLowSourceIC.categories P t ht.le) P.originalLowLaw)
  (π : JointProfile D P t ht)
  (upperBid : ℝ→ℝ) (hupperBid : Measurable upperBid)
  (hfloor : ∀v,t< v→ H≤ upperBid v)

local notation "E" => regions D P hdR H hUH
local notation "z" => activeMass P.theta*P.zeta*powerTail P.M 10 t
variable (hrare : (1-D.ξ)*D.U+D.ξ*D.U*((N+1:ℝ)*
  ((activeMass P.theta*P.zeta*powerTail P.M 10 t)/
    (partialMass+activeMass P.theta*P.zeta*powerTail P.M 10 t)))≤ D.R)

private lemma castMarketRare {n : ℕ} {x y p q : ℝ}
    (h : x+y*((n+1:ℝ)*p)≤q) : x+y*((((n+1:ℕ):ℝ))*p)≤q := by
  simpa only [Nat.cast_add,Nat.cast_one] using h
local notation "Γ" => NativeZeroNoiseSource.game D P t ht hdR H hUH L.joint π
  upperBid hupperBid hfloor (N+1) (castMarketRare hrare)
local notation "K" => localData D P t ht hdR H hUH L.joint π
  upperBid hupperBid hfloor N (castMarketRare hrare)
local notation "Γ₀" => coreGame D P t ht hdR H hUH L.joint π
  upperBid hupperBid hfloor N (castMarketRare hrare)
local notation "G" => (ProbabilityMeasure.map (Subtype.val L.joint) measurable_snd.aemeasurable : ProbabilityMeasure (LowValue P.d0))
local notation "ν" => Measure.pi (fun _ : Fin N=> rivalLaw (lowMass P.theta)
  (activeMass P.theta-z) (partialMass+z) (realLowLaw (G : Measure (LowValue P.d0))))

include t ht L π upperBid hupperBid hfloor hrare in
theorem original_load_le (γ : ℝ) (hγ : 0≤ γ) (hN : 0< N)
    (hcap : (D.c:ℝ)≤(N:ℝ)*(activeMass P.theta-z-γ))
    (i : Fin (N+1)) (a : JointAction 2) (hk : a.routeCount=2) (hb : a.bid≤ P.d0) :
    ((problem Γ i).outcome a).load≤2*Real.exp (-2*(N:ℝ)*γ^2) := by
  have hp := NativeLowSourceIC.original_profiles_on_menu P t ht.le E rfl N D.c
    D.ξ D.width D.regimeShare D.eA D.eR D.F D.hξ D.hξ1 D.hw
    D.regimeShare.2.1 D.regimeShare.2.2 L
    («partial» D P t ht π) (active D P t ht π) upperBid hupperBid hfloor
    hrare (base_duplicate_gap D) D.eta D.heta0 D.heta1
  have hr := NativeLowSourceIC.original_deleted_row P t ht.le E rfl N D.c
    D.ξ D.width D.regimeShare D.eA D.eR D.F D.hξ D.hξ1 D.hw
    D.regimeShare.2.1 D.regimeShare.2.2 L
    («partial» D P t ht π) (active D P t ht π) upperBid hupperBid hfloor
    hrare (base_duplicate_gap D) D.eta D.heta0 D.heta1 i
  have hl := load_le_active_underflow K Γ₀ rfl hp i ν hr a hk hb
  rw [sourceGame_problem]
  apply hl.trans
  exact mul_le_mul_of_nonneg_left
    (active_underflow_le (lowMass P.theta) (activeMass P.theta-z) (partialMass+z)
      P.low_mass_pos.le (P.movingActiveMass_positive t ht.le).le
      (add_nonneg (by norm_num [partialMass]) (P.tailMass_nonneg t ht.le))
      (by linarith [mass_sum P.theta]) (realLowLaw (G : Measure (LowValue P.d0)))
      N D.c hN γ hγ hcap) (by norm_num)

include D t ht hdR H hUH L π upperBid hupperBid hfloor in
theorem original_lowCondition :
    ∀ᵐx ∂(Γ).F⊗ₘ(Γ).σ,lowCondition P.d0 x := by
  rw [game_original_joint]
  filter_upwards [source_bands D P t ht hdR H hUH L.joint π
    upperBid hupperBid hfloor] with x hx
  intro hv
  rcases hx with hx | hx | hx | hx
  · exact ⟨hx.2.2,hx.2.1⟩
  · exfalso
    linarith [hx.1.1,hv.2,P.low_partial_gap]
  · exfalso
    linarith [hx.1.1,hv.2,P.low_partial_gap,P.partial_active_gap,P.w_pos]
  · exfalso
    linarith [hx.1,hv.2,ht,P.low_partial_gap,P.partial_active_gap,
      P.active_tail_gap,P.w_pos]

include t ht hdR H hUH L π upperBid hupperBid hfloor hrare in
theorem original_conditional_load_le (γ : ℝ) (hγ : 0≤ γ) (hN : 0< N)
    (hcap : (D.c:ℝ)≤(N:ℝ)*(activeMass P.theta-z-γ))
    (v : ℝ) (hv : v∈Icc (0:ℝ) P.d0) :
    (conditionalTypeCountLaw (LowFixedValueVersions.game Γ P.d0) (Nat.succ_pos N) v).load≤
      2*Real.exp (-2*(N:ℝ)*γ^2) :=
  conditional_load_of_bounds Γ (Nat.succ_pos N) P.d0 P.d0_pos.le
    (original_lowCondition D P t ht hdR H hUH N L π upperBid hupperBid hfloor hrare)
    _ (original_load_le D P t ht hdR H hUH N L π upperBid hupperBid hfloor hrare
      γ hγ hN hcap) v hv

include t ht hdR H hUH L π upperBid hupperBid hfloor hrare in
theorem original_conditional_mass_error (γ : ℝ) (hγ : 0≤ γ) (hN : 0< N)
    (hcap : (D.c:ℝ)≤(N:ℝ)*(activeMass P.theta-z-γ))
    (v : ℝ) (hv : v∈Icc (0:ℝ) P.d0) (r : Fin 3) :
    |(conditionalTypeCountLaw (LowFixedValueVersions.game Γ P.d0) (Nat.succ_pos N) v).mass r-
      (FiniteLaw.dirac (0:Fin 3)).mass r|≤2*Real.exp (-2*(N:ℝ)*γ^2) :=
  (mass_error_le_load _ r).trans
    (original_conditional_load_le D P t ht hdR H hUH N L π upperBid hupperBid hfloor
      hrare γ hγ hN hcap v hv)

end Finite

def gap (P : ValueParameters) : ℝ := (activeMass P.theta-99/200)/4
def error (P : ValueParameters) (N : ℕ) : ℝ := 2*Real.exp (-2*(N:ℝ)*(gap P)^2)

theorem gap_positive (P : ValueParameters) : 0< gap P := by
  have hθ0 := P.theta_pos
  have hθ1 := P.theta_small
  dsimp [gap,activeMass,delta]
  nlinarith

theorem error_tendsto_zero (P : ValueParameters) :
    Tendsto (error P) atTop (𝓝 0) := by
  have hg := gap_positive P
  have hc : 0<2*(gap P)^2 := by positivity
  have he := Real.tendsto_exp_neg_atTop_nhds_zero.comp
    ((tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ=>(N:ℝ)) atTop atTop).const_mul_atTop hc)
  convert! he.const_mul 2 using 1
  · funext N
    dsimp only [error,Function.comp_apply]
    congr 2
    ring
  · simp

theorem eventually_room (P : ValueParameters) :
    ∀ᶠN : ℕ in atTop,0< N ∧ P.M< movingThreshold (N+1) ∧
      (Markets.capacity (N+1):ℝ)≤(N:ℝ)*
        (activeMass P.theta-
          activeMass P.theta*P.zeta*powerTail P.M 10 (movingThreshold (N+1))-gap P) := by
  have hg := gap_positive P
  have ht := movingThreshold_tendsto.comp (tendsto_add_atTop_nat 1)
  have hm := (OriginalMovingLow.raw_mass_tendsto P).comp (tendsto_add_atTop_nat 1)
  have hn : Tendsto (fun N : ℕ=>2*(N:ℝ)*gap P) atTop atTop := by
    convert! (tendsto_natCast_atTop_atTop :
      Tendsto (fun N : ℕ=>(N:ℝ)) atTop atTop).const_mul_atTop
      (show 0<2*gap P by positivity) using 1
    funext N
    ring
  filter_upwards [eventually_gt_atTop (0:ℕ),ht.eventually_gt_atTop P.M,
    hm.eventually_lt_const hg,hn.eventually_ge_atTop (99/200:ℝ)] with N hN hM hmass hroom
  dsimp only [Function.comp_apply] at hM hmass
  have hmass' : activeMass P.theta*P.zeta*powerTail P.M 10
      (movingThreshold (N+1))≤ gap P := by
    rw [powerTail_ten P.M _ P.M_pos (P.M_pos.trans hM)]
    exact hmass.le
  have hc := Markets.capacity_le (N+1)
  refine ⟨hN,hM,?_⟩
  simp only [Nat.cast_add,Nat.cast_one] at hc
  have hb := mul_le_mul_of_nonneg_left hmass' (Nat.cast_nonneg N : (0:ℝ)≤ N)
  have hid : (N:ℝ)*(activeMass P.theta-2*gap P)=
      (99/200:ℝ)*N+2*(N:ℝ)*gap P := by
    unfold gap
    ring
  calc
    (Markets.capacity (N+1):ℝ)≤(99/200:ℝ)*(N+1) := hc
    _ ≤ (N:ℝ)*(activeMass P.theta-2*gap P) := by rw [hid];nlinarith
    _ ≤ _ := by nlinarith

structure Market (P : ValueParameters) (N : ℕ) where
  data : Data
  cap : data.c=Markets.capacity (N+1)
  threshold : P.M< movingThreshold (N+1)
  low_gap : P.d0< data.R
  H : ℝ
  upper_gap : data.U< H
  low : ActualAtomlessLowLimit N P.d0 data.ξ data.c
    (NativeLowSourceIC.categories P (movingThreshold (N+1)) threshold.le) P.originalLowLaw
  joint : JointProfile data P (movingThreshold (N+1)) threshold
  upperBid : ℝ→ℝ
  upperBid_measurable : Measurable upperBid
  upper_floor : ∀v,movingThreshold (N+1)< v→ H≤ upperBid v
  rare : (1-data.ξ)*data.U+data.ξ*data.U*((N+1:ℝ)*
    ((activeMass P.theta*P.zeta*powerTail P.M 10 (movingThreshold (N+1)))/
      (partialMass+activeMass P.theta*P.zeta*powerTail P.M 10 (movingThreshold (N+1)))))≤ data.R

namespace Market
variable {P : ValueParameters} {N : ℕ} (A : Market P N)
def native : FiniteGame (N+1) 2 A.data.c NativeLocalPolicy.Seed :=
  NativeZeroNoiseSource.game A.data P (movingThreshold (N+1)) A.threshold
    A.low_gap A.H A.upper_gap A.low.joint A.joint A.upperBid A.upperBid_measurable
    A.upper_floor (N+1) (castMarketRare A.rare)
def specified : FiniteGame (N+1) 2 A.data.c NativeLocalPolicy.Seed :=
  LowFixedValueVersions.game A.native P.d0

theorem specified_joint : A.specified.F⊗ₘA.specified.σ=A.native.F⊗ₘA.native.σ :=
  LowFixedValueVersions.joint_eq A.native P.d0
    (original_lowCondition A.data P _ A.threshold A.low_gap A.H A.upper_gap N A.low A.joint
      A.upperBid A.upperBid_measurable A.upper_floor A.rare)

theorem specified_outside_low (v : ℝ) (hv : v∉Icc (0:ℝ) P.d0) :
    A.specified.σ v=A.native.σ v :=
  strategy_outside_low A.native P.d0 v hv
end Market

theorem original_fixed_value_count_limit (P : ValueParameters)
    (N : ℕ→ℕ) (hN : Tendsto N atTop atTop) (A : ∀k,Market P (N k)) :
    ∀v∈Icc (0:ℝ) P.d0,∀r : Fin 3,
      Tendsto (fun k=>(conditionalTypeCountLaw (A k).specified (Nat.succ_pos (N k)) v).mass r)
        atTop (𝓝 ((FiniteLaw.dirac (0:Fin 3)).mass r)) := by
  apply mass_tendsto_zero_count (fun k=>(A k).native) (fun k=> Nat.succ_pos (N k))
    P.d0 P.d0_pos.le (B:=fun k=> error P (N k))
  · intro k
    exact original_lowCondition (A k).data P _ (A k).threshold (A k).low_gap (A k).H
      (A k).upper_gap (N k) (A k).low (A k).joint (A k).upperBid (A k).upperBid_measurable
      (A k).upper_floor (A k).rare
  · exact error_tendsto_zero P |>.comp hN
  · filter_upwards [hN.eventually (eventually_room P)] with k hk
    intro i a ha hb
    exact original_load_le (A k).data P _ (A k).threshold (A k).low_gap (A k).H
      (A k).upper_gap (N k) (A k).low (A k).joint (A k).upperBid (A k).upperBid_measurable
      (A k).upper_floor (A k).rare (gap P) (gap_positive P).le hk.1
      (by rw [(A k).cap];exact hk.2.2) i a ha hb

theorem original_cutoff_count_limit (P : ValueParameters)
    (N : ℕ→ℕ) (hN : Tendsto N atTop atTop) (A : ∀k,Market P (N k)) (r : Fin 3) :
    Tendsto (fun k=>(conditionalTypeCountLaw (A k).specified (Nat.succ_pos (N k))
      (P.d0/(100*lowMass P.theta))).mass r)
      atTop (𝓝 ((FiniteLaw.dirac (0:Fin 3)).mass r)) :=
  original_fixed_value_count_limit P N hN A P.cutoff
    ⟨P.cutoff_in_low_band.1.le,P.cutoff_in_low_band.2.le⟩ r

end FCAppendix.Affine.Tail04.SourceLowCountLaws
