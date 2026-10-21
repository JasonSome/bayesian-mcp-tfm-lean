import FCAppendix.Affine.Hybrid.Tail03.Parameters
import FCAppendix.Affine.Hybrid.Tail03.Pareto
import FCAppendix.Affine.Hybrid.Tail03.LimitAlgebra
import FCAppendix.Finite.ConditionalCountLaw
import FCAppendix.Finite.ReceiptBoundsAE
import FCAppendix.PayOnce.BroadcastRescue
import FCAppendix.PayOnce.KernelAgreement

noncomputable section
namespace FCAppendix.Affine.Hybrid.Tail03
open MeasureTheory ProbabilityTheory Game Bayes Set Filter Topology
open scoped BigOperators

structure NativeFinite (F : ProbabilityMeasure ℝ) (eta : ℝ) (m : ℕ) where

  Seed : Type
  [seedSpace : MeasurableSpace Seed]
  game : Bayes.FiniteGame m 2 (sourceCapacity m) Seed
  posterior : Bayes.PosteriorSystem game
  values : game.F=(F : Measure ℝ)
  eta_pos : 0 < eta
  eta_lt_one : eta < 1
  bid_rule : game.A=Schedule.affine 2 eta eta_pos.le eta_lt_one.le
  base_rule : game.G=Schedule.once 2
  fee : game.g=0
  m_pos : 0 < m
  capacity_pos : 1 ≤ sourceCapacity m
  capacity_lt : sourceCapacity m < m
  users : Bayes.UsersOptimal game
  proposers : Bayes.PosteriorProposerOptimalAE game posterior

  proposers_full : Bayes.PosteriorProposerOptimal game posterior
  bid_atomless : NullSingletonClass (Bayes.realBidLaw game)
  visible_atomless : Bayes.VisibleAtomless game

attribute [instance] NativeFinite.seedSpace

namespace NativeFinite

lemma equilibrium {F eta m} (N : NativeFinite F eta m) :
    Bayes.IsBayesianEquilibrium N.game :=
  ⟨N.users,⟨N.posterior,N.proposers_full⟩⟩

def conditionalCount {F eta m} (N : NativeFinite F eta m) (v : ℝ) : CountLaw 2 :=
  Bayes.conditionalTypeCountLaw N.game N.m_pos v

lemma conditionalCount_mass_eq_average {F eta m} (N : NativeFinite F eta m)
    (v : ℝ) (r : Fin 3) :
    (N.conditionalCount v).mass r =
      (∑ i : Fin m,(Bayes.typeOutcome N.game i v).mass r)/(m:ℝ) := rfl

lemma conditionalCount_mass_error {F eta m} (N : NativeFinite F eta m)
    (v z eps : ℝ) (r : Fin 3)
    (h : ∀ i : Fin m,|(Bayes.typeOutcome N.game i v).mass r-z|≤eps) :
    |(N.conditionalCount v).mass r-z|≤eps := by
  have hm : (0 : ℝ) < (m : ℝ) := by exact_mod_cast N.m_pos
  rw [N.conditionalCount_mass_eq_average]
  calc
    |(∑ i : Fin m,(Bayes.typeOutcome N.game i v).mass r)/(m:ℝ)-z| =
        |(∑ i : Fin m,((Bayes.typeOutcome N.game i v).mass r-z))/(m:ℝ)| := by
      congr 1
      rw [Finset.sum_sub_distrib]
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      field_simp
    _ = |∑ i : Fin m,((Bayes.typeOutcome N.game i v).mass r-z)|/(m:ℝ) := by
      rw [abs_div,abs_of_pos hm]
    _ ≤ (∑ i : Fin m,|(Bayes.typeOutcome N.game i v).mass r-z|)/(m:ℝ) :=
      div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) hm.le
    _ ≤ (∑ _i : Fin m,eps)/(m:ℝ) :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum (fun i _=>h i)) hm.le
    _ = eps := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      exact mul_div_cancel_left₀ eps (ne_of_gt hm)

lemma measurable_conditionalCount_mass {F eta m} (N : NativeFinite F eta m)
    (r : Fin 3) : Measurable (fun v=>(N.conditionalCount v).mass r) := by
  simpa only [conditionalCount,FiniteLaw.expect_singleton] using
    Bayes.measurable_conditionalTypeCountLaw_expect N.game N.m_pos
      (fun j=> if j=r then (1:ℝ) else 0)

lemma coverage_eq_original_integral {F eta m} (N : NativeFinite F eta m) :
    Bayes.finiteCoverage N.game=∫v,(N.conditionalCount v).success ∂(F : Measure ℝ) := by
  rw [←N.values]
  exact (Bayes.integral_conditionalTypeCountLaw_success N.game N.m_pos).symm

lemma load_eq_original_integral {F eta m} (N : NativeFinite F eta m) :
    Bayes.finiteLoad N.game=∫v,(N.conditionalCount v).load ∂(F : Measure ℝ) := by
  rw [←N.values]
  exact (Bayes.integral_conditionalTypeCountLaw_load N.game N.m_pos).symm

end NativeFinite

structure ActualTwoCoefficientFamilies (F : ProbabilityMeasure ℝ) (eta1 eta2 : ℝ) where
  firstMarket : ℕ
  firstMarket_pos : 0 < firstMarket
  lower : ∀m,firstMarket≤ m → NativeFinite F eta1 m
  upper : ∀m,firstMarket≤ m → NativeFinite F eta2 m

namespace ActualTwoCoefficientFamilies

abbrev Market {F eta1 eta2} (f : ActualTwoCoefficientFamilies F eta1 eta2) :=
  {m : ℕ // f.firstMarket≤ m}

def lowerAt {F eta1 eta2} (f : ActualTwoCoefficientFamilies F eta1 eta2) (m : f.Market) :=
  f.lower m.1 m.2
def upperAt {F eta1 eta2} (f : ActualTwoCoefficientFamilies F eta1 eta2) (m : f.Market) :=
  f.upper m.1 m.2

theorem common_conull_all_actions {F eta1 eta2}
    (f : ActualTwoCoefficientFamilies F eta1 eta2) :
    ∀ᵐv ∂(F : Measure ℝ),∀m : f.Market,∀i : Fin m.1,
      (∀ᵐa ∂(f.lowerAt m).game.σ v,∀raw : JointAction 2,
        (Bayes.problem (f.lowerAt m).game i).payoff v raw ≤
          (Bayes.problem (f.lowerAt m).game i).payoff v a) ∧
      (∀ᵐa ∂(f.upperAt m).game.σ v,∀raw : JointAction 2,
        (Bayes.problem (f.upperAt m).game i).payoff v raw ≤
          (Bayes.problem (f.upperAt m).game i).payoff v a) := by
  apply ae_all_iff.mpr
  intro m
  apply ae_all_iff.mpr
  intro i
  have hl := (f.lowerAt m).users i
  have hu := (f.upperAt m).users i
  rw [(f.lowerAt m).values] at hl
  rw [(f.upperAt m).values] at hu
  exact hl.and hu

end ActualTwoCoefficientFamilies

structure OneCommonSubsequenceLimits {eta1 eta2 : ℝ} (p : Parameters eta1 eta2)
    (f : ActualTwoCoefficientFamilies (commonLaw p) eta1 eta2) where
  index : ℕ→ f.Market
  increasing : StrictMono (fun k=>(index k).1)
  multiplier : Fin 2→ℝ
  multiplier_mem : multiplier∈p.rect.box
  lowerLaw : ℝ→ CountLaw 2
  upperLaw : ℝ→ CountLaw 2
  measurable_lower : ∀r,Measurable (fun v=>(lowerLaw v).mass r)
  measurable_upper : ∀r,Measurable (fun v=>(upperLaw v).mass r)
  ae_count_limits : ∀ᵐv ∂(commonLaw p : Measure ℝ),∀r,
    Tendsto (fun k=>((f.lowerAt (index k)).conditionalCount v).mass r) atTop
      (𝓝 ((lowerLaw v).mass r)) ∧
    Tendsto (fun k=>((f.upperAt (index k)).conditionalCount v).mass r) atTop
      (𝓝 ((upperLaw v).mass r))
  fixed_tail_count_limits : ∀v,p.tailFloor≤ v → ∀r,
    Tendsto (fun k=>((f.lowerAt (index k)).conditionalCount v).mass r) atTop
      (𝓝 ((lowerLaw v).mass r)) ∧
    Tendsto (fun k=>((f.upperAt (index k)).conditionalCount v).mass r) atTop
      (𝓝 ((upperLaw v).mass r))
  lower_tail : ∀v,p.tailFloor≤ v → lowerLaw v=FiniteLaw.dirac (1 : Fin 3)
  upper_tail_failure : ∀v,p.tailFloor≤ v →
    (upperLaw v).mass 0=1-served p.center multiplier (p.boundary.response multiplier v)
  upper_tail_duplicates : ∀v,p.tailFloor≤ v →
    (upperLaw v).mass 2=duplicates p.center multiplier (p.boundary.response multiplier v)
  low_lower : ∀ᵐv ∂bandMeasure 0 p.d0,(lowerLaw v).success=0
  low_upper : ∀ᵐv ∂bandMeasure 0 p.d0,(upperLaw v).success=0
  partial_lower : ∀ᵐv ∂bandMeasure (2-p.valueWidth) (2+p.valueWidth),
    1-oneMixedMass p.center≤(lowerLaw v).success
  partial_upper : ∀ᵐv ∂bandMeasure (2-p.valueWidth) (2+p.valueWidth),
    (upperLaw v).success=1-p.center.theta
  fixed_upper_lower : ∀ᵐv ∂fixedUpperValueMeasure p.lawInput,(lowerLaw v).success=1
  underfill_lower : Tendsto (fun k=>
    2*(sourceCapacity (index k).1 : ℝ)/(index k).1-
      Bayes.finiteLoad (f.lowerAt (index k)).game) atTop (𝓝 0)
  underfill_upper : Tendsto (fun k=>
    2*(sourceCapacity (index k).1 : ℝ)/(index k).1-
      Bayes.finiteLoad (f.upperAt (index k)).game) atTop (𝓝 0)

structure BothOriginalFiniteFamiliesAndLimits {eta1 eta2 : ℝ}
    (p : Parameters eta1 eta2) where
  families : ActualTwoCoefficientFamilies (commonLaw p) eta1 eta2
  limits : OneCommonSubsequenceLimits p families

end FCAppendix.Affine.Hybrid.Tail03
