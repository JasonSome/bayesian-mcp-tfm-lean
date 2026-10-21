import FCAppendix.Affine.Tail04.OriginalCompactLaws

noncomputable section
namespace FCAppendix.Affine.Tail04
open MeasureTheory ProbabilityTheory Set Game Bayes

theorem joint_event_mass_from_value {A : Type*} [MeasurableSpace A]
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (σ : Kernel ℝ A) [IsMarkovKernel σ]
    (E : Set (ℝ × A)) (V : Set ℝ) (hV : MeasurableSet V)
    (hshape : ∀ᵐ x ∂F ⊗ₘ σ, x ∈ E ↔ x.1 ∈ V) :
    (F ⊗ₘ σ).real E = F.real V := by
  have he : (F ⊗ₘ σ) E = (F ⊗ₘ σ) (Prod.fst ⁻¹' V) :=
    measure_congr (hshape.mono (fun x hx => propext hx))
  rw [measureReal_def, he, ← Measure.fst_apply hV, Measure.fst_compProd]
  rfl

namespace ValueParameters
open OriginalValues

variable (P : ValueParameters) (E : Observable.Regions)

theorem strategy_private_mass
    (σ : Kernel ℝ (JointAction 2)) [IsMarkovKernel σ]
    (t : ℝ) (ht : P.M ≤ t)
    (hshape : ∀ᵐ x ∂valueLaw P ⊗ₘ σ,
      x.2.bid ∈ E.privateBids ↔ x.1 ∈ P.privateValues t) :
    (valueLaw P ⊗ₘ σ).real E.privateJointEvent = partialMass +
      activeMass P.theta*P.zeta*powerTail P.M 10 t := by
  rw [joint_event_mass_from_value (valueLaw P) σ E.privateJointEvent
    (P.privateValues t) (measurableSet_Icc.union measurableSet_Ioi) hshape,
    P.private_mass t ht]

theorem strategy_upper_mass
    (σ : Kernel ℝ (JointAction 2)) [IsMarkovKernel σ]
    (t : ℝ) (ht : P.M ≤ t)
    (hshape : ∀ᵐ x ∂valueLaw P ⊗ₘ σ, E.H ≤ x.2.bid ↔ t < x.1) :
    (valueLaw P ⊗ₘ σ).real E.upperJointEvent =
      activeMass P.theta*P.zeta*powerTail P.M 10 t := by
  rw [joint_event_mass_from_value (valueLaw P) σ E.upperJointEvent
    (Ioi t) measurableSet_Ioi hshape, P.real_tail t ht]

theorem native_source_private_share {m c : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (Γ : FiniteGame m 2 c Seed)
    (hF : Γ.F = valueLaw P) (t : ℝ) (ht : P.M ≤ t)
    (hprivate : ∀ᵐ x ∂Γ.F ⊗ₘ Γ.σ,
      x.2.bid ∈ E.privateBids ↔ x.1 ∈ P.privateValues t)
    (hupper : ∀ᵐ x ∂Γ.F ⊗ₘ Γ.σ, E.H ≤ x.2.bid ↔ t < x.1)
    (j : Fin 2) :
    (cond (userLaw Γ) (E.privateJointEvent ×ˢ oneRouteEvent j)).real
      (E.upperJointEvent ×ˢ (univ : Set (Equiv.Perm (Fin 2)))) =
      (activeMass P.theta*P.zeta*powerTail P.M 10 t) /
        (partialMass+activeMass P.theta*P.zeta*powerTail P.M 10 t) := by
  have hp : (Γ.F ⊗ₘ Γ.σ).real E.privateJointEvent = partialMass +
      activeMass P.theta*P.zeta*powerTail P.M 10 t := by
    rw [hF] at hprivate ⊢
    exact P.strategy_private_mass E Γ.σ t ht hprivate
  have hu : (Γ.F ⊗ₘ Γ.σ).real E.upperJointEvent =
      activeMass P.theta*P.zeta*powerTail P.M 10 t := by
    rw [hF] at hupper ⊢
    exact P.strategy_upper_mass E Γ.σ t ht hupper
  exact E.native_private_mark_share_of_masses Γ j partialMass _
    (by norm_num [partialMass]) (P.tailMass_nonneg t ht) hp hu

theorem native_moving_private_share {m c : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (Γ : FiniteGame m 2 c Seed)
    (hF : Γ.F = valueLaw P) (ht : P.M ≤ movingThreshold m)
    (hprivate : ∀ᵐ x ∂Γ.F ⊗ₘ Γ.σ,
      x.2.bid ∈ E.privateBids ↔ x.1 ∈ P.privateValues (movingThreshold m))
    (hupper : ∀ᵐ x ∂Γ.F ⊗ₘ Γ.σ,
      E.H ≤ x.2.bid ↔ movingThreshold m < x.1)
    (j : Fin 2) :
    (cond (userLaw Γ) (E.privateJointEvent ×ˢ oneRouteEvent j)).real
      (E.upperJointEvent ×ˢ (univ : Set (Equiv.Perm (Fin 2)))) =
      movingPrivateShare partialMass (activeMass P.theta) P.zeta P.M m := by
  rw [P.native_source_private_share E Γ hF _ ht hprivate hupper j,
    powerTail_ten P.M _ P.M_pos (P.M_pos.trans_le ht)]
  rfl

theorem native_action_event {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Γ : FiniteGame m 2 c Seed) (A : Set (JointAction 2)) (hA : MeasurableSet A) :
    (Hybrid.nativeActionLaw Γ).real A =
      (Γ.F ⊗ₘ Γ.σ).real {x | x.2 ∈ A} := by
  rw [Hybrid.nativeActionLaw, measureReal_def, Measure.map_apply measurable_snd hA]
  rfl

theorem native_source_category_masses {m c : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (Γ : FiniteGame m 2 c Seed)
    (hF : Γ.F = valueLaw P) (t : ℝ) (ht : P.M ≤ t)
    (hlow : ∀ᵐ x ∂Γ.F ⊗ₘ Γ.σ, x.2.bid ≤ E.d ↔ x.1 ≤ P.d0)
    (hprivate : ∀ᵐ x ∂Γ.F ⊗ₘ Γ.σ,
      x.2.bid ∈ E.privateBids ↔ x.1 ∈ P.privateValues t) :
    (Hybrid.nativeActionLaw Γ).real E.lowActions = lowMass P.theta ∧
    (Hybrid.nativeActionLaw Γ).real E.commonActions =
      activeMass P.theta-activeMass P.theta*P.zeta*powerTail P.M 10 t ∧
    (Hybrid.nativeActionLaw Γ).real E.privateActions =
      partialMass+activeMass P.theta*P.zeta*powerTail P.M 10 t := by
  have hs : (Hybrid.nativeActionLaw Γ).real E.lowActions = lowMass P.theta := by
    rw [native_action_event Γ E.lowActions E.measurableSet_lowActions]
    rw [hF] at hlow ⊢
    change (valueLaw P ⊗ₘ Γ.σ).real {x | x.2.bid ≤ E.d} = lowMass P.theta
    exact (joint_event_mass_from_value (valueLaw P) Γ.σ
      {x : ℝ × JointAction 2 | x.2.bid ≤ E.d} (Iic P.d0) measurableSet_Iic hlow).trans P.low_mass
  have hh : (Hybrid.nativeActionLaw Γ).real E.privateActions =
      partialMass+activeMass P.theta*P.zeta*powerTail P.M 10 t := by
    rw [native_action_event Γ E.privateActions E.measurableSet_privateActions]
    change (Γ.F ⊗ₘ Γ.σ).real E.privateJointEvent = _
    rw [hF] at hprivate ⊢
    exact P.strategy_private_mass E Γ.σ t ht hprivate
  have hpartition := congrArg (fun μ : Measure (JointAction 2) => μ.real univ)
    (E.action_partition (Hybrid.nativeActionLaw Γ))
  rw [measureReal_add_apply, measureReal_add_apply] at hpartition
  simp only [measureReal_def, Measure.restrict_apply_univ, measure_univ,
    ENNReal.toReal_one] at hpartition
  change (Hybrid.nativeActionLaw Γ).real E.lowActions +
    (Hybrid.nativeActionLaw Γ).real E.commonActions +
    (Hybrid.nativeActionLaw Γ).real E.privateActions = 1 at hpartition
  refine ⟨hs, ?_, hh⟩
  have hsum := mass_sum P.theta
  rw [hs, hh] at hpartition
  linarith

theorem native_source_row {m c : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (Γ : FiniteGame m 2 c Seed)
    (hF : Γ.F = valueLaw P) (t : ℝ) (ht : P.M ≤ t)
    (hlow : ∀ᵐ x ∂Γ.F ⊗ₘ Γ.σ, x.2.bid ≤ E.d ↔ x.1 ≤ P.d0)
    (hprivate : ∀ᵐ x ∂Γ.F ⊗ₘ Γ.σ,
      x.2.bid ∈ E.privateBids ↔ x.1 ∈ P.privateValues t) :
    (userLaw Γ).map (E.nativeRow Γ) =
      LowBody.rivalLaw (lowMass P.theta)
        (activeMass P.theta-activeMass P.theta*P.zeta*powerTail P.M 10 t)
        (partialMass+activeMass P.theta*P.zeta*powerTail P.M 10 t)
        ((cond (Hybrid.nativeActionLaw Γ) E.lowActions).map (fun a => a.bid)) := by
  obtain ⟨hs, ha, hh⟩ := P.native_source_category_masses E Γ hF t ht hlow hprivate
  rw [E.native_row_law Γ, hs, ha, hh]

end ValueParameters
end FCAppendix.Affine.Tail04

namespace FCAppendix.Affine.Tail04.OriginalValues
export FCAppendix.Affine.Tail04.ValueParameters (strategy_private_mass strategy_upper_mass native_source_private_share native_moving_private_share native_action_event native_source_category_masses native_source_row)
end FCAppendix.Affine.Tail04.OriginalValues
