import FCAppendix.Affine.Tail04.ConditionalVersions
import FCAppendix.Affine.Tail04.RawRouteCounts
import FCAppendix.Affine.Tail04.OriginalValueLaw

noncomputable section
namespace FCAppendix.Affine.Tail04.PartialFixedValueVersions
open MeasureTheory ProbabilityTheory Set Classical Game Bayes Filter Topology
open ConditionalVersions
open scoped BigOperators

def condition (vL vU R Up : ℝ) (x : ℝ×JointAction 2) : Prop :=
  x.1∈Icc vL vU → x.2.routeCount=1 ∧ x.2.bid∈Icc R Up

lemma measurableSet_condition (vL vU R Up : ℝ) : MeasurableSet {x | condition vL vU R Up x} := by
  have he : {x | condition vL vU R Up x}=(Prod.fst ⁻¹' Icc vL vU)ᶜ∪
      {x : ℝ×JointAction 2 | x.2.routeCount=1 ∧ x.2.bid∈Icc R Up} := by
    ext x;simp [condition,imp_iff_not_or]
  rw [he]
  exact (measurableSet_Icc.preimage measurable_fst).compl.union
    ((measurableSet_eq_fun ((measurable_routeCount 2).comp measurable_snd) measurable_const).inter
      (measurableSet_Icc.preimage ((measurable_bid 2).comp measurable_snd)))

def bottom (R : ℝ) (hR : 0≤ R) : JointAction 2 := RawRoutes.action R hR 1

variable {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

def strategy (Γ : FiniteGame m 2 c Seed) (vL vU R Up : ℝ) (hR : 0≤ R) : Kernel ℝ (JointAction 2) :=
  repair Γ.σ (measurableSet_condition vL vU R Up) (fun _=> bottom R hR) measurable_const

instance strategy_markov (Γ : FiniteGame m 2 c Seed) (vL vU R Up : ℝ) (hR : 0≤ R) :
    IsMarkovKernel (strategy Γ vL vU R Up hR) := by
  unfold strategy;infer_instance

def game (Γ : FiniteGame m 2 c Seed) (vL vU R Up : ℝ) (hR : 0≤ R) : FiniteGame m 2 c Seed :=
  withStrategy Γ (strategy Γ vL vU R Up hR)

lemma fixed_value_support (Γ : FiniteGame m 2 c Seed) (vL vU R Up : ℝ) (hR : 0≤ R)
    (hRUp : R≤ Up) (v : ℝ) (hv : v∈Icc vL vU) :
    ∀ᵐa ∂strategy Γ vL vU R Up hR v,a.routeCount=1 ∧ a.bid∈Icc R Up := by
  filter_upwards [repair_fixed_value_support Γ.σ (measurableSet_condition vL vU R Up)
    (fun _=> bottom R hR) measurable_const v] with a ha
  rcases ha with ha | rfl
  · exact ha hv
  · exact ⟨rfl,le_rfl,hRUp⟩

lemma outside (Γ : FiniteGame m 2 c Seed) (vL vU R Up : ℝ) (hR : 0≤ R)
    (v : ℝ) (hv : v∉Icc vL vU) : strategy Γ vL vU R Up hR v=Γ.σ v := by
  apply repair_apply_good
  change Γ.σ v {a | ¬condition vL vU R Up (v,a)}=0
  have he : {a : JointAction 2 | ¬condition vL vU R Up (v,a)}=∅ := by
    ext a;simp [condition,hv]
  rw [he,measure_empty]

variable (Γ : FiniteGame m 2 c Seed) (vL vU R Up : ℝ) (hR : 0≤ R)
  (hs : ∀ᵐx ∂Γ.F⊗ₘΓ.σ,condition vL vU R Up x)

include hs in
lemma strategy_ae_eq : strategy Γ vL vU R Up hR=ᵐ[Γ.F] Γ.σ :=
  repair_ae_eq Γ.F Γ.σ (measurableSet_condition vL vU R Up)
    (fun _=> bottom R hR) measurable_const (Measure.ae_ae_of_ae_compProd hs)

include hs in
lemma joint_eq : (game Γ vL vU R Up hR).F⊗ₘ(game Γ vL vU R Up hR).σ=Γ.F⊗ₘΓ.σ :=
  withStrategy_joint Γ _ (strategy_ae_eq Γ vL vU R Up hR hs)

include hs in
lemma problem_eq (i : Fin m) : problem (game Γ vL vU R Up hR) i=problem Γ i :=
  withStrategy_problem Γ _ (strategy_ae_eq Γ vL vU R Up hR hs) i

include hs in
lemma equilibrium (hΓ : IsBayesianEquilibrium Γ) : IsBayesianEquilibrium (game Γ vL vU R Up hR) :=
  withStrategy_equilibrium Γ _ (strategy_ae_eq Γ vL vU R Up hR hs) hΓ

include hs in
theorem conditional_eq_outside (hm : 0< m) (v : ℝ) (hv : v∉Icc vL vU) :
    conditionalTypeCountLaw (game Γ vL vU R Up hR) hm v=
      conditionalTypeCountLaw Γ hm v := by
  apply FiniteLaw.ext
  intro r
  have hk : (game Γ vL vU R Up hR).σ v=Γ.σ v :=
    outside Γ vL vU R Up hR v hv
  rw [←FiniteLaw.expect_singleton,←FiniteLaw.expect_singleton,
    conditionalTypeCountLaw_expect,conditionalTypeCountLaw_expect]
  simp_rw [problem_eq Γ vL vU R Up hR hs,hk]

theorem conditional_mass_bound {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (G : FiniteGame m 2 c Seed) (hm : 0< m) (v : ℝ) (J : CountLaw 2) (err : ℝ) (r : Fin 3)
    (hbound : ∀i,∀ᵐa ∂G.σ v,|((problem G i).outcome a).mass r-J.mass r|≤ err) :
    |(conditionalTypeCountLaw G hm v).mass r-J.mass r|≤ err := by
  have hi (i : Fin m) :
      |(∫a,((problem G i).outcome a).mass r ∂G.σ v)-J.mass r|≤ err := by
    have hint := FiniteLaw.integrable_expect (G.σ v) (problem G i).outcome
      (measurable_outcome_mass G i) (fun q : Fin 3=> if q=r then 1 else 0)
    simp only [FiniteLaw.expect_singleton] at hint
    have hh := norm_integral_le_of_norm_le_const (μ:=G.σ v)
      (f:=fun a : JointAction 2=>((problem G i).outcome a).mass r-J.mass r) (C:=err)
      ((hbound i).mono fun a ha=> by simpa only [Real.norm_eq_abs] using ha)
    rw [integral_sub hint (integrable_const (J.mass r))] at hh
    simpa only [integral_const,measureReal_def,measure_univ,ENNReal.toReal_one,
      one_smul,mul_one,Real.norm_eq_abs] using hh
  have hmass : (conditionalTypeCountLaw G hm v).mass r=
      (∑i,∫a,((problem G i).outcome a).mass r ∂G.σ v)/(m:ℝ) := by
    simpa only [FiniteLaw.expect_singleton] using conditionalTypeCountLaw_expect G hm v
      (fun q : Fin 3=> if q=r then 1 else 0)
  rw [hmass]
  have hmR : (0:ℝ)< m := Nat.cast_pos.mpr hm
  apply abs_le.mpr
  constructor
  · have hh := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin m)))=>(abs_le.mp (hi i)).1)
    simp only [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hh
    have hq : J.mass r-err≤
        (∑i,∫a,((problem G i).outcome a).mass r ∂G.σ v)/(m:ℝ) :=
      (le_div_iff₀ hmR).mpr (by nlinarith)
    linarith
  · have hh := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin m)))=>(abs_le.mp (hi i)).2)
    simp only [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hh
    have hq : (∑i,∫a,((problem G i).outcome a).mass r ∂G.σ v)/(m:ℝ)≤ err+J.mass r :=
      (div_le_iff₀ hmR).mpr (by nlinarith)
    linarith

include hs in
theorem conditional_from_native (hm : 0< m) (hRUp : R≤ Up) (J : CountLaw 2) (err : ℝ)
    (hcount : ∀i a,a.routeCount=1→ a.bid∈Icc R Up→∀r,
      |((problem Γ i).outcome a).mass r-J.mass r|≤ err)
    (v : ℝ) (hv : v∈Icc vL vU) (r : Fin 3) :
    |(conditionalTypeCountLaw (game Γ vL vU R Up hR) hm v).mass r-J.mass r|≤ err := by
  apply conditional_mass_bound
  intro i
  rw [problem_eq Γ vL vU R Up hR hs i]
  filter_upwards [fixed_value_support Γ vL vU R Up hR hRUp v hv] with a ha
  exact hcount i a ha.1 ha.2 r

end FCAppendix.Affine.Tail04.PartialFixedValueVersions
