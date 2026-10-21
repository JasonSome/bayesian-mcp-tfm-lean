import FCAppendix.Affine.Uniform07Finishing.Crossover.OptimizerCover
import FCAppendix.Affine.LowBody.HiddenRoute
import FCAppendix.Affine.Uniform07.Parameters
import Mathlib.MeasureTheory.Measure.Support

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing.Crossover
open MeasureTheory ProbabilityTheory Bayes Game Set Filter Topology Classical
open scoped BigOperators

namespace Physical

variable {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

def action (k : Fin 3) (b : ℝ) : JointAction 2 where
  bid := max b 0
  bid_nonneg := le_max_right _ _
  routeCount := k.val
  routeCount_le := by omega

def one (b : ℝ) : JointAction 2 := action 1 b
def two (b : ℝ) : JointAction 2 := action 2 b

@[simp] theorem one_bid {b : ℝ} (hb : 0≤ b) : (one b).bid=b := by
  simp [one,action,max_eq_left hb]

@[simp] theorem two_bid {b : ℝ} (hb : 0≤ b) : (two b).bid=b := by
  simp [two,action,max_eq_left hb]

@[simp] theorem one_routes (b : ℝ) : (one b).routeCount=1 := rfl
@[simp] theorem two_routes (b : ℝ) : (two b).routeCount=2 := rfl

theorem raw_one_eq (a : JointAction 2) (ha : a.routeCount=1) : a=one a.bid := by
  cases a with
  | mk b hb k hk =>
    simp only at ha
    subst k
    simp [one,action,max_eq_left hb]

theorem raw_two_eq (a : JointAction 2) (ha : a.routeCount=2) : a=two a.bid := by
  cases a with
  | mk b hb k hk =>
    simp only at ha
    subst k
    simp [two,action,max_eq_left hb]

def q (Γ : FiniteGame m 2 c Seed) (i : Fin m) (b : ℝ) : ℝ :=
  meanAcceptProb Γ i b

def success (Γ : FiniteGame m 2 c Seed) (i : Fin m) (b : ℝ) : ℝ :=
  ((problem Γ i).outcome (two b)).success

def duplicate (Γ : FiniteGame m 2 c Seed) (i : Fin m) (b : ℝ) : ℝ :=
  ((problem Γ i).outcome (two b)).duplicates

def rank (Γ : FiniteGame m 2 c Seed) (t b : ℝ) : ℝ :=
  (Γ.F ⊗ₘ Γ.σ).real {x : ℝ × JointAction 2 | x.1≤ t ∧ x.2.bid≤ b}

def lowerBidMeasure (Γ : FiniteGame m 2 c Seed) (t : ℝ) : Measure ℝ :=
  ((Γ.F ⊗ₘ Γ.σ).restrict {x : ℝ × JointAction 2 | x.1≤ t}).map
    (fun x : ℝ × JointAction 2 => x.2.bid)

theorem rank_eq_lowerBidMeasure (Γ : FiniteGame m 2 c Seed) (t b : ℝ) :
    rank Γ t b=(lowerBidMeasure Γ t).real (Iic b) := by
  have hb : Measurable (fun x : ℝ × JointAction 2 => x.2.bid) :=
    (measurable_bid 2).comp measurable_snd
  change ((Γ.F ⊗ₘ Γ.σ) {x : ℝ × JointAction 2 | x.1≤ t ∧ x.2.bid≤ b}).toReal =
    ((((Γ.F ⊗ₘ Γ.σ).restrict {x : ℝ × JointAction 2 | x.1≤ t}).map
      (fun x : ℝ × JointAction 2 => x.2.bid)) (Iic b)).toReal
  rw [Measure.map_apply hb measurableSet_Iic,Measure.restrict_apply (hb measurableSet_Iic)]
  have he : (fun x : ℝ × JointAction 2 => x.2.bid) ⁻¹' Iic b ∩ {x | x.1≤ t}=
      {x : ℝ × JointAction 2 | x.1≤ t ∧ x.2.bid≤ b} := by
    ext x
    simp only [mem_inter_iff,mem_preimage,mem_Iic,mem_setOf_eq,and_comm]
  rw [he]

theorem rank_monotone (Γ : FiniteGame m 2 c Seed) (t : ℝ) :
    Monotone (rank Γ t) := by
  intro b b' hbb'
  unfold rank
  exact ENNReal.toReal_mono (measure_ne_top _ _)
    (measure_mono fun x hx => ⟨hx.1,hx.2.trans hbb'⟩)

theorem rank_constant_on_unused_gap (Γ : FiniteGame m 2 c Seed) (t : ℝ)
    [NullSingletonClass (lowerBidMeasure Γ t)]
    {x y : ℝ} (_hxy : x≤ y)
    (hgap : ∀ z∈Ioo x y, z∉(lowerBidMeasure Γ t).support) :
    ∀ z∈Icc x y, rank Γ t z=rank Γ t y := by
  intro z hz
  rw [rank_eq_lowerBidMeasure,rank_eq_lowerBidMeasure]
  apply measureReal_congr
  have hy : ∀ᵐ w ∂lowerBidMeasure Γ t, w≠y := by
    exact measure_eq_zero_iff_ae_notMem.mp (measure_singleton y)
  filter_upwards [Measure.support_mem_ae (μ := lowerBidMeasure Γ t),hy] with w hw hwy
  apply propext
  constructor
  · exact fun hwz => hwz.trans hz.2
  · intro hwy'
    by_contra hwz
    have hzw : z< w := lt_of_not_ge hwz
    have hwylt : w< y := lt_of_le_of_ne hwy' hwy
    exact hgap w ⟨hz.1.trans_lt hzw,hwylt⟩ hw

theorem rank_hasDerivAt_zero_on_gap (Γ : FiniteGame m 2 c Seed) (t : ℝ)
    [NullSingletonClass (lowerBidMeasure Γ t)]
    {x y z : ℝ} (hz : z∈Ioo x y)
    (hgap : ∀ u∈Ioo x y, u∉(lowerBidMeasure Γ t).support) :
    HasDerivAt (rank Γ t) 0 z := by
  have hr := rank_constant_on_unused_gap Γ t (hz.1.trans hz.2).le hgap
  apply (hasDerivAt_const z (rank Γ t y)).congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hz.1 hz.2] with u hu
  exact hr u ⟨hu.1.le,hu.2.le⟩

def pureRank (m c : ℕ) (t w : ℝ) : ℝ :=
  binomBelow (m-1) ((1+t)/2-w) c

theorem q_nonneg (Γ : FiniteGame m 2 c Seed) (i : Fin m) (b : ℝ) :
    0≤ q Γ i b := by
  unfold q meanAcceptProb acceptProb
  positivity

theorem duplicate_nonneg (Γ : FiniteGame m 2 c Seed) (i : Fin m) (b : ℝ) :
    0≤ duplicate Γ i b :=
  ((problem Γ i).outcome (two b)).duplicates_nonneg

theorem success_eq_two_q_sub_duplicate
    (Γ : FiniteGame m 2 c Seed) (i : Fin m) {b : ℝ} (hb : 0≤ b) :
    success Γ i b=2*q Γ i b-duplicate Γ i b := by
  have hl := load_eq_mean Γ (by norm_num : 0<2) i (two b)
  simp only [two_routes,two_bid hb,Nat.cast_ofNat] at hl
  unfold success duplicate q CountLaw.duplicates
  linarith

theorem duplicate_le_q (Γ : FiniteGame m 2 c Seed) (i : Fin m)
    {b : ℝ} (hb : 0≤ b) : duplicate Γ i b≤ q Γ i b := by
  have hs := meanAcceptProb_le_success Γ (by norm_num : 0<2) i (two b)
    (by norm_num [two,action])
  simp only [two_bid hb] at hs
  change q Γ i b≤ success Γ i b at hs
  rw [success_eq_two_q_sub_duplicate Γ i hb] at hs
  linarith

theorem one_payoff (Γ : FiniteGame m 2 c Seed) (hg : Γ.g=0)
    (i : Fin m) (v : ℝ) {b : ℝ} (hb : 0≤ b) :
    (problem Γ i).payoff v (one b)=utilityOne v b (q Γ i b) := by
  rw [singleton_payoff Γ (by norm_num : 0<2) i (one b) (one_routes b),hg]
  simp only [one_bid hb,sub_zero,q,utilityOne]

theorem two_payoff (Γ : FiniteGame m 2 c Seed) {eta : ℝ}
    (heta0 : 0≤ eta) (heta1 : eta≤ 1)
    (hA : Γ.A=Schedule.affine 2 eta heta0 heta1) (hg : Γ.g=0)
    (i : Fin m) (v : ℝ) {b : ℝ} (hb : 0≤ b) :
    (problem Γ i).payoff v (two b)=
      utilityTwo eta v b (q Γ i b) (duplicate Γ i b) := by
  rw [LowBody.native_affine_zero_fee_payoff Γ heta0 heta1 hA hg]
  simp only [two_bid hb]
  change (v-b)*success Γ i b-eta*b*duplicate Γ i b=_
  rw [success_eq_two_q_sub_duplicate Γ i hb]
  rfl

theorem raw_route_difference (Γ : FiniteGame m 2 c Seed) {eta : ℝ}
    (heta0 : 0≤ eta) (heta1 : eta≤ 1)
    (hA : Γ.A=Schedule.affine 2 eta heta0 heta1) (hg : Γ.g=0)
    (i : Fin m) (v : ℝ) (a : JointAction 2) (ha : a.routeCount=1) :
    (problem Γ i).payoff v (LowBody.addSecondRoute a)-(problem Γ i).payoff v a=
      (v-a.bid)*(q Γ i a.bid-duplicate Γ i a.bid)-
        eta*a.bid*duplicate Γ i a.bid := by
  have htwo : LowBody.addSecondRoute a=two a.bid := by
    simpa only [LowBody.addSecondRoute] using
      raw_two_eq (LowBody.addSecondRoute a) rfl
  have hone : (problem Γ i).payoff v a=utilityOne v a.bid (q Γ i a.bid) := by
    rw [singleton_payoff Γ (by norm_num : 0<2) i a ha,hg]
    simp only [sub_zero,q,utilityOne]
  rw [htwo,two_payoff Γ heta0 heta1 hA hg i v a.bid_nonneg,hone]
  exact route_difference eta v a.bid (q Γ i a.bid) (duplicate Γ i a.bid)

theorem raw_singleton_optimum_scalar (Γ : FiniteGame m 2 c Seed)
    (hg : Γ.g=0) (i : Fin m) (v : ℝ) (a : JointAction 2)
    (ha : a.routeCount=1)
    (hopt : ∀ a' : JointAction 2, a'.routeCount=1 →
      (problem Γ i).payoff v a'≤(problem Γ i).payoff v a) :
    ∀ z≥ 0, utilityOne v z (q Γ i z)≤ utilityOne v a.bid (q Γ i a.bid) := by
  intro z hz
  have h := hopt (one z) (one_routes z)
  rw [one_payoff Γ hg i v hz,
    singleton_payoff Γ (by norm_num : 0<2) i a ha,hg] at h
  simpa only [sub_zero,q,utilityOne] using h

theorem raw_singleton_optimum_scalar_below (Γ : FiniteGame m 2 c Seed)
    (hg : Γ.g=0) (i : Fin m) (v U : ℝ) (a : JointAction 2)
    (ha : a.routeCount=1)
    (hopt : ∀ a' : JointAction 2, a'.routeCount=1 → a'.bid≤ U →
      (problem Γ i).payoff v a'≤(problem Γ i).payoff v a) :
    ∀ z∈Icc (0:ℝ) U,
      utilityOne v z (q Γ i z)≤ utilityOne v a.bid (q Γ i a.bid) := by
  intro z hz
  have h := hopt (one z) (one_routes z) (by simpa only [one_bid hz.1] using hz.2)
  rw [one_payoff Γ hg i v hz.1,
    singleton_payoff Γ (by norm_num : 0<2) i a ha,hg] at h
  simpa only [sub_zero,q,utilityOne] using h

theorem low_raw_singleton_optimizer_loses (Γ : FiniteGame m 2 c Seed)
    {eta v ell dupBound lowTop : ℝ} (heta0 : 0≤ eta) (heta1 : eta≤ 1)
    (hA : Γ.A=Schedule.affine 2 eta heta0 heta1) (hg : Γ.g=0)
    (i : Fin m) (hv : 0< v) (hell : 0< ell) (hsmall : dupBound< ell/2)
    (hhalf : ell≤ q Γ i (v/2))
    (hdup : ∀ b∈Icc (0:ℝ) lowTop, duplicate Γ i b≤ dupBound)
    (a : JointAction 2) (ha : a.routeCount=1) (halow : a.bid≤ lowTop)
    (hopt : ∀ a' : JointAction 2, a'.routeCount=1 →
      (problem Γ i).payoff v a'≤(problem Γ i).payoff v a) :
    (problem Γ i).payoff v a<(problem Γ i).payoff v (LowBody.addSecondRoute a) := by
  apply LowBody.native_one_route_optimum_strictly_improved Γ heta0 heta1 hA hg
    i hv hell hsmall a (one (v/2)) ha (one_routes (v/2))
    (one_bid (by positivity : 0≤ v/2))
  · simpa only [one_bid (by positivity : 0≤ v/2),q] using hhalf
  · exact hopt
  · have htwo : LowBody.addSecondRoute a=two a.bid := by
      simpa only [LowBody.addSecondRoute] using
        raw_two_eq (LowBody.addSecondRoute a) rfl
    rw [htwo]
    exact hdup a.bid ⟨a.bid_nonneg,halow⟩

structure CanonicalEvent (Γ : FiniteGame m 2 c Seed) where
  event : ℝ → Set (Sample m 2 Seed)
  measurable : ∀ b, MeasurableSet (event b)

def canonicalSuccess (Γ : FiniteGame m 2 c Seed) (i : Fin m)
    (B : CanonicalEvent Γ) (b : ℝ) : ℝ :=
  ∫ ω in B.event b, successIndicator (focalCount Γ i (two b) ω).val ∂sampleLaw Γ

def canonicalDuplicate (Γ : FiniteGame m 2 c Seed) (i : Fin m)
    (B : CanonicalEvent Γ) (b : ℝ) : ℝ :=
  ∫ ω in B.event b,
    ((focalCount Γ i (two b) ω).val : ℝ)-
      successIndicator (focalCount Γ i (two b) ω).val ∂sampleLaw Γ

def canonicalMarginal (Γ : FiniteGame m 2 c Seed) (i : Fin m)
    (B : CanonicalEvent Γ) (b : ℝ) : ℝ :=
  (canonicalSuccess Γ i B b+canonicalDuplicate Γ i B b)/2

def comparisonMarginal (Γ : FiniteGame m 2 c Seed) (i : Fin m)
    (B : CanonicalEvent Γ) (t b : ℝ) : ℝ :=
  pureRank m c t (rank Γ t b)+canonicalMarginal Γ i B b

def successError (Γ : FiniteGame m 2 c Seed) (i : Fin m)
    (B : CanonicalEvent Γ) (t b : ℝ) : ℝ :=
  success Γ i b-
    (2*comparisonMarginal Γ i B t b-canonicalDuplicate Γ i B b)

def duplicateError (Γ : FiniteGame m 2 c Seed) (i : Fin m)
    (B : CanonicalEvent Γ) (b : ℝ) : ℝ :=
  duplicate Γ i b-canonicalDuplicate Γ i B b

theorem actual_marginal_error_identity (Γ : FiniteGame m 2 c Seed) (i : Fin m)
    (B : CanonicalEvent Γ) (t : ℝ) {b : ℝ} (hb : 0≤ b) :
    q Γ i b=comparisonMarginal Γ i B t b+
      (successError Γ i B t b+duplicateError Γ i B b)/2 := by
  have h := success_eq_two_q_sub_duplicate Γ i hb
  unfold successError duplicateError
  linarith

end Physical
end FCAppendix.Affine.Uniform07Finishing.Crossover
