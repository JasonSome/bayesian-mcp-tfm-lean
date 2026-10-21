import FCAppendix.Affine.Tail04.NativeLowCountBounds
import FCAppendix.Affine.Tail04.ConditionalVersions

noncomputable section
namespace FCAppendix.Affine.Tail04.LowFixedValueVersions
open MeasureTheory ProbabilityTheory Set Classical Game Bayes Filter Topology
open Hybrid NativeLowCountBounds ConditionalVersions NativeMenuReports
open scoped BigOperators

def lowCondition (d : ℝ) (x : ℝ×JointAction 2) : Prop :=
  x.1∈Icc (0:ℝ) d → x.2.routeCount=2 ∧ x.2.bid≤ d

lemma measurableSet_lowCondition (d : ℝ) :
    MeasurableSet {x | lowCondition d x} := by
  have he : {x | lowCondition d x}=
      (Prod.fst ⁻¹' Icc (0:ℝ) d)ᶜ ∪
        {x : ℝ×JointAction 2 | x.2.routeCount=2 ∧ x.2.bid≤ d} := by
    ext x
    simp [lowCondition,imp_iff_not_or]
  rw [he]
  exact (measurableSet_Icc.preimage measurable_fst).compl.union
    ((measurableSet_eq_fun ((measurable_routeCount 2).comp measurable_snd)
      measurable_const).inter
      (measurableSet_le ((measurable_bid 2).comp measurable_snd) measurable_const))

def zeroBroadcast : JointAction 2 := NativeLowIncentives.broadcast 0 le_rfl

def strategy {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Γ : FiniteGame m 2 c Seed) (d : ℝ) : Kernel ℝ (JointAction 2) :=
  repair Γ.σ (measurableSet_lowCondition d) (fun _=> zeroBroadcast) measurable_const

instance strategy_markov {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Γ : FiniteGame m 2 c Seed) (d : ℝ) : IsMarkovKernel (strategy Γ d) := by
  unfold strategy
  infer_instance

def game {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Γ : FiniteGame m 2 c Seed) (d : ℝ) : FiniteGame m 2 c Seed :=
  withStrategy Γ (strategy Γ d)

section Repair
variable {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
  (Γ : FiniteGame m 2 c Seed) (d : ℝ)

theorem fixed_value_support (hd : 0≤ d) (v : ℝ) (hv : v∈Icc (0:ℝ) d) :
    ∀ᵐa ∂strategy Γ d v,a.routeCount=2 ∧ a.bid≤ d := by
  have hs := repair_fixed_value_support Γ.σ (measurableSet_lowCondition d)
    (fun _=> zeroBroadcast) measurable_const v
  filter_upwards [hs] with a ha
  rcases ha with ha | rfl
  · exact ha hv
  · exact ⟨rfl,hd⟩

theorem strategy_outside_low (v : ℝ) (hv : v∉Icc (0:ℝ) d) :
    strategy Γ d v=Γ.σ v := by
  apply repair_apply_good
  change Γ.σ v {a | ¬lowCondition d (v,a)}=0
  have he : {a : JointAction 2 | ¬lowCondition d (v,a)}=∅ := by
    ext a
    simp [lowCondition,hv]
  rw [he,measure_empty]

variable (hs : ∀ᵐx ∂Γ.F⊗ₘΓ.σ,lowCondition d x)

include hs in
theorem strategy_ae_eq : strategy Γ d=ᵐ[Γ.F] Γ.σ :=
  repair_ae_eq Γ.F Γ.σ (measurableSet_lowCondition d)
    (fun _=> zeroBroadcast) measurable_const (Measure.ae_ae_of_ae_compProd hs)

include hs in
theorem joint_eq : (game Γ d).F⊗ₘ(game Γ d).σ=Γ.F⊗ₘΓ.σ :=
  withStrategy_joint Γ (strategy Γ d) (strategy_ae_eq Γ d hs)

include hs in
theorem problem_eq (i : Fin m) : problem (game Γ d) i=problem Γ i :=
  withStrategy_problem Γ (strategy Γ d) (strategy_ae_eq Γ d hs) i

include hs in
theorem equilibrium (hΓ : IsBayesianEquilibrium Γ) :
    IsBayesianEquilibrium (game Γ d) :=
  withStrategy_equilibrium Γ (strategy Γ d) (strategy_ae_eq Γ d hs) hΓ

end Repair

theorem mass_error_le_load (K : CountLaw 2) (r : Fin 3) :
    |K.mass r-(FiniteLaw.dirac (0:Fin 3)).mass r|≤ K.load := by
  have h := Counts.count_masses K
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun j=>Fin.elim0 j))) r
  · change |K.mass 0-(FiniteLaw.dirac (0:Fin 3)).mass 0|≤K.load
    simp only [FiniteLaw.dirac,ite_true]
    rw [h.1,show 1-K.success-1= -K.success by ring,abs_neg,
      abs_of_nonneg K.success_nonneg]
    exact K.success_le_load
  · change |K.mass 1-(FiniteLaw.dirac (0:Fin 3)).mass 1|≤K.load
    simp only [FiniteLaw.dirac,show (1:Fin 3)≠0 by decide,ite_false]
    rw [sub_zero,abs_of_nonneg (K.nonneg 1),h.2.1]
    have hS := K.success_le_load
    have hD := K.duplicates_nonneg
    linarith
  · change |K.mass 2-(FiniteLaw.dirac (0:Fin 3)).mass 2|≤K.load
    simp only [FiniteLaw.dirac,show (2:Fin 3)≠0 by decide,ite_false]
    rw [sub_zero,abs_of_nonneg (K.nonneg 2),h.2.2]
    dsimp only [CountLaw.duplicates]
    linarith [K.success_nonneg]

theorem conditional_load_of_bounds {m c : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (Γ : FiniteGame m 2 c Seed) (hm : 0< m)
    (d : ℝ) (hd : 0≤ d)
    (hs : ∀ᵐx ∂Γ.F⊗ₘΓ.σ,lowCondition d x)
    (B : ℝ)
    (hload : ∀i a,a.routeCount=2→ a.bid≤ d→((problem Γ i).outcome a).load≤ B)
    (v : ℝ) (hv : v∈Icc (0:ℝ) d) :
    (conditionalTypeCountLaw (game Γ d) hm v).load≤ B := by
  let Q := game Γ d
  have hi (i : Fin m) : (∫a,((problem Q i).outcome a).load∂Q.σ v)≤ B := by
    rw [problem_eq Γ d hs i]
    have hint := FiniteLaw.integrable_expect (Q.σ v) (problem Γ i).outcome
      (measurable_outcome_mass Γ i) (fun r : Fin 3=>(r.val:ℝ))
    have hh : (∫a,((problem Γ i).outcome a).load∂Q.σ v)≤∫_a,B∂Q.σ v := by
      apply integral_mono_ae hint (integrable_const B)
      filter_upwards [fixed_value_support Γ d hd v hv] with a ha
      exact hload i a ha.1 ha.2
    simpa only [integral_const,probReal_univ,smul_eq_mul,one_mul] using hh
  rw [conditionalTypeCountLaw_load]
  apply (div_le_iff₀ (Nat.cast_pos.mpr hm)).mpr
  have hsum := Finset.sum_le_sum
    (fun i (_ : i∈(Finset.univ : Finset (Fin m)))=> hi i)
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_comm]
    using hsum

theorem mass_tendsto_zero_count {m c : ℕ→ℕ} {Seed : ℕ→ Type*}
    [∀n,MeasurableSpace (Seed n)] (Γ : ∀n,FiniteGame (m n) 2 (c n) (Seed n))
    (hm : ∀n,0< m n) (d : ℝ) (hd : 0≤ d)
    (hs : ∀n,∀ᵐx ∂(Γ n).F⊗ₘ(Γ n).σ,lowCondition d x)
    (B : ℕ→ℝ) (hB : Tendsto B atTop (𝓝 0))
    (hload : ∀ᶠn in atTop,∀i a,a.routeCount=2→ a.bid≤ d→
      ((problem (Γ n) i).outcome a).load≤ B n) :
    ∀v∈Icc (0:ℝ) d,∀r : Fin 3,
      Tendsto (fun n=>(conditionalTypeCountLaw (game (Γ n) d) (hm n) v).mass r)
        atTop (𝓝 ((FiniteLaw.dirac (0:Fin 3)).mass r)) := by
  intro v hv r
  have he : Tendsto (fun n=>
      |(conditionalTypeCountLaw (game (Γ n) d) (hm n) v).mass r-
        (FiniteLaw.dirac (0:Fin 3)).mass r|) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun _=> abs_nonneg _)) _ hB
    filter_upwards [hload] with n hn
    exact (mass_error_le_load _ r).trans
      (conditional_load_of_bounds (Γ n) (hm n) d hd (hs n) (B n) hn v hv)
  exact tendsto_iff_norm_sub_tendsto_zero.mpr (by simpa only [Real.norm_eq_abs] using he)

section NativeBound
variable {N c : ℕ} (D : NativeLocalPolicy.Data (N+1) c)
  (Γ : FiniteGame (N+1) 2 c NativeLocalPolicy.Seed)
  (hpolicy : Γ.policy=D.completedPolicy)
  (hprofiles : ∀ᵐp ∂userProfileLaw Γ,∀l,MenuAction D.E (p l).1.2)
  (ν : Measure (Fin N→ LowBody.RowRival))
  (hlaw : ∀i,(userProfileLaw Γ).map (NativeLowIntegration.rowProfile D.E i)=ν)
  (hs : ∀ᵐx ∂Γ.F⊗ₘΓ.σ,lowCondition D.E.d x)

include hpolicy hprofiles hlaw hs in
theorem conditional_load_le (v : ℝ) (hv : v∈Icc (0:ℝ) D.E.d) :
    (conditionalTypeCountLaw (game Γ D.E.d) (Nat.succ_pos N) v).load≤
      2*ν.real (activeUnderflow c) := by
  let Q := game Γ D.E.d
  let B := 2*ν.real (activeUnderflow c)
  have hi (i : Fin (N+1)) :
      (∫a,((problem Q i).outcome a).load∂Q.σ v)≤ B := by
    rw [problem_eq Γ D.E.d hs i]
    have hint := FiniteLaw.integrable_expect (Q.σ v) (problem Γ i).outcome
      (measurable_outcome_mass Γ i) (fun r : Fin 3=>(r.val:ℝ))
    have hh : (∫a,((problem Γ i).outcome a).load∂Q.σ v)≤
        ∫_a,B∂Q.σ v := by
      apply integral_mono_ae hint (integrable_const B)
      filter_upwards [fixed_value_support Γ D.E.d D.E.d_nonneg v hv] with a ha
      exact load_le_active_underflow D Γ hpolicy hprofiles i ν (hlaw i) a ha.1 ha.2
    simpa only [integral_const,probReal_univ,smul_eq_mul,one_mul] using hh
  rw [conditionalTypeCountLaw_load]
  have hsum := Finset.sum_le_sum (fun i (_ : i∈(Finset.univ : Finset (Fin (N+1))))=> hi i)
  have hm : (0:ℝ)< N+1 := by positivity
  apply (div_le_iff₀ (by exact_mod_cast Nat.succ_pos N)).mpr
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
    Nat.cast_add,Nat.cast_one,mul_comm] using hsum

include hpolicy hprofiles hlaw hs in
theorem conditional_mass_error_le (v : ℝ) (hv : v∈Icc (0:ℝ) D.E.d) (r : Fin 3) :
    |(conditionalTypeCountLaw (game Γ D.E.d) (Nat.succ_pos N) v).mass r-
      (FiniteLaw.dirac (0:Fin 3)).mass r|≤2*ν.real (activeUnderflow c) :=
  (mass_error_le_load _ r).trans
    (conditional_load_le D Γ hpolicy hprofiles ν hlaw hs v hv)

end NativeBound
end FCAppendix.Affine.Tail04.LowFixedValueVersions
