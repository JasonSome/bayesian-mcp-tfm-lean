import FCAppendix.Affine.Tail04.SourceOrderedNoisyFixedPoint

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedOriginalNoisySequence
open MeasureTheory ProbabilityTheory Set Filter Topology Classical Hybrid
open Existence.Distributional OriginalValues SourceTailNoisyFixedPoint
open FiniteTailNoisyGame

structure Sequence (D : Data) (P : ValueParameters) (t : ℝ) (ht : P.M< t) (N : ℕ) where
  eps : ℕ → unitInterval
  law : ℕ → JointProfile D P t ht
  limit : JointProfile D P t ht
  noise_positive : ∀ j,0<(eps j:ℝ)
  noise_small : ∀ j,(eps j:ℝ)< D.eps
  noise_tendsto : Tendsto eps atTop (𝓝 0)
  law_tendsto : Tendsto law atTop (𝓝 limit)
  optimal : ∀ j k,AllActionOptimal (law j k)
    (fun x => SourceOrderedNoisyFixedPoint.payoff (atNoise D (eps j) (noise_positive j) (noise_small j)) P t ht N k (law j,x))
  conditional : ∀ j,∃ σ : ∀ k : Fin 3,Kernel (ActiveValue (valueLo P k) (valueHi P t k))
      (ActiveBaseBid (bidLo D k) (bidHi D k)),
    (∀ k,IsMarkovKernel (σ k)) ∧
    (∀ k,originalValueLaw P t ht k ⊗ₘ σ k=((law j k).1 : Measure _)) ∧
    (∀ k,∀ᵐ v ∂originalValueLaw P t ht k,∀ᵐ b ∂σ k v,
      ∀ b' : ActiveBaseBid (bidLo D k) (bidHi D k),
        SourceOrderedNoisyFixedPoint.payoff (atNoise D (eps j) (noise_positive j) (noise_small j)) P t ht N k (law j,(v,b'))≤
          SourceOrderedNoisyFixedPoint.payoff (atNoise D (eps j) (noise_positive j) (noise_small j)) P t ht N k (law j,(v,b)))
  physical_tendsto : ∀ k,Tendsto
    (fun j => Hybrid.activeUniversalNoisyLaw (bidLo_pos D k) (bidLo_le_hi D k)
      (originalValueLaw P t ht k) (eps j,law j k)) atTop
      (𝓝 (Hybrid.activeUniversalNoisyLaw (bidLo_pos D k) (bidLo_le_hi D k)
        (originalValueLaw P t ht k) (0,limit k)))

theorem exists_sequence (D : Data) (hbudget : D.eps≤1)
    (P : ValueParameters) (t : ℝ) (ht : P.M< t) (N : ℕ) :
    Nonempty (Sequence D P t ht N) := by
  obtain ⟨eps,π,π₀,hε,htε,hopt,htπ,hphys⟩ :=
    SourceOrderedNoisyFixedPoint.exists_original_joint_noisy_sequence D hbudget P t ht N
  refine ⟨⟨eps,π,π₀,fun j => (hε j).1,fun j => (hε j).2,htε,htπ,?_,?_,hphys⟩⟩
  · intro j k
    obtain ⟨σ,hσ,hjoint,hall,hcond⟩ := hopt j
    have hk := hall k
    rw [SourceOrderedNoisyFixedPoint.sequencePayoff_eq D P t ht N (eps j) (hε j).1 (hε j).2] at hk
    convert! hk using 1
  · intro j
    obtain ⟨σ,hσ,hjoint,hall,hcond⟩ := hopt j
    refine ⟨σ,hσ,hjoint,?_⟩
    rw [SourceOrderedNoisyFixedPoint.sequencePayoff_eq D P t ht N (eps j) (hε j).1 (hε j).2] at hcond
    convert! hcond using 1

namespace Sequence
variable {D : Data} {P : ValueParameters} {t : ℝ} {ht : P.M< t} {N : ℕ}
  (S : Sequence D P t ht N)

def data (j : ℕ) : Data := atNoise D (S.eps j) (S.noise_positive j) (S.noise_small j)

@[simp] lemma data_eps (j : ℕ) : (S.data j).eps=(S.eps j:ℝ) := rfl
@[simp] lemma data_R (j : ℕ) : (S.data j).R=D.R := rfl
@[simp] lemma data_Up (j : ℕ) : (S.data j).Up=D.Up := rfl
@[simp] lemma data_U (j : ℕ) : (S.data j).U=D.U := rfl
@[simp] lemma data_c (j : ℕ) : (S.data j).c=D.c := rfl
@[simp] lemma data_xi (j : ℕ) : (S.data j).ξ=D.ξ := rfl

theorem physical_cap_le (j : ℕ) : (S.data j).B≤ D.B := by
  change D.U*(1+(S.eps j:ℝ)) ≤ D.U*(1+D.eps)
  exact mul_le_mul_of_nonneg_left (add_le_add (le_refl 1) (S.noise_small j).le)
    ((by norm_num : (0:ℝ)≤1).trans D.hU)

theorem partial_cap_le (j : ℕ) : (S.data j).V≤ D.V := by
  change D.Up*(1+(S.eps j:ℝ)) ≤ D.Up*(1+D.eps)
  exact mul_le_mul_of_nonneg_left (add_le_add (le_refl 1) (S.noise_small j).le) (D.hR.le.trans D.hRUp)

theorem rare_guard (hrare : (1-D.ξ)*D.B+D.ξ*D.B*((N+1:ℕ)*
    (tailMass P t/(partialMass+tailMass P t)))≤ D.R) (j : ℕ) :
    (1-(S.data j).ξ)*(S.data j).B+(S.data j).ξ*(S.data j).B*((N+1:ℕ)*
      (tailMass P t/(partialMass+tailMass P t)))≤(S.data j).R := by
  have hp : 0≤(N+1:ℕ)*(tailMass P t/(partialMass+tailMass P t)) :=
    mul_nonneg (Nat.cast_nonneg _) (div_nonneg (SourceTailNoisyFixedPoint.tailMass_nonneg P t ht.le)
      (add_nonneg (by norm_num [partialMass]) (SourceTailNoisyFixedPoint.tailMass_nonneg P t ht.le)))
  exact le_trans
    (add_le_add
      (mul_le_mul_of_nonneg_left (S.physical_cap_le j) (sub_nonneg.mpr D.hξ1.le))
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (S.physical_cap_le j) D.hξ.le) hp)) hrare

theorem noise_real_tendsto : Tendsto (fun j => (S.eps j:ℝ)) atTop (𝓝 0) :=
  continuous_subtype_val.continuousAt.tendsto.comp S.noise_tendsto

def realBaseLaw (k : Fin 3) (π : JointProfile D P t ht) : ProbabilityMeasure ℝ :=
  (π k).1.map measurable_snd.subtype_val.aemeasurable

include P t ht in
lemma continuous_realBaseLaw (k : Fin 3) :
    Continuous (realBaseLaw (D:=D) (P:=P) (t:=t) (ht:=ht) k) :=
  (ProbabilityMeasure.continuous_map (continuous_subtype_val.comp continuous_snd)).comp
    (continuous_subtype_val.comp (continuous_apply k))

theorem realBaseLaw_tendsto (k : Fin 3) :
    Tendsto (fun j => realBaseLaw k (S.law j)) atTop (𝓝 (realBaseLaw k S.limit)) :=
  (continuous_realBaseLaw (D:=D) (P:=P) (t:=t) (ht:=ht) k).continuousAt.tendsto.comp S.law_tendsto

end Sequence
end FCAppendix.Affine.Tail04.OrderedOriginalNoisySequence
