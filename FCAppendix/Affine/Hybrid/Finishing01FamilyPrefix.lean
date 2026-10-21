import FCAppendix.Affine.Hybrid.Finishing01Definitions

noncomputable section
namespace FCAppendix.Affine.Hybrid.Finish01
open Set Filter Topology MeasureTheory ProbabilityTheory Classical
open Existence.Distributional
namespace Primitives
variable (P : Primitives)

def prefixJoint (mu : Measure P.Value) [IsProbabilityMeasure mu] : Law (A:=P.Bid) mu :=
  ⟨productLaw (⟨mu,inferInstance⟩ : ProbabilityMeasure P.Value)
    (diracProba (⟨P.L,le_rfl,P.L_lt_U.le⟩ : P.Bid)),by
      change (mu.prod (Measure.dirac (⟨P.L,le_rfl,P.L_lt_U.le⟩ : P.Bid))).fst = mu
      simp [Measure.fst,Measure.map_fst_prod]⟩

lemma prefixJoint_original_marginal (mu : Measure P.Value) [IsProbabilityMeasure mu] :
    ((P.prefixJoint mu).1 : Measure (P.Value×P.Bid)).fst=mu :=
  (P.prefixJoint mu).property

lemma prefixJoint_measure (mu : Measure P.Value) [IsProbabilityMeasure mu] :
    ((P.prefixJoint mu).1 : Measure (P.Value×P.Bid)) =
      mu.prod (Measure.dirac (⟨P.L,le_rfl,P.L_lt_U.le⟩ : P.Bid)) := rfl

def extend_joint_prefix (mu : Measure P.Value) [IsProbabilityMeasure mu]
    (M0 : ℕ) (tail : ∀ M : ℕ, M0 ≤ M → Law (A:=P.Bid) mu) :
    ℕ → Law (A:=P.Bid) mu :=
  fun M => if h : M0 ≤ M then tail M h else P.prefixJoint mu

def extend_low_prefix (M0 : ℕ)
    (tail : ∀ M : ℕ, M0 ≤ M → ProbabilityMeasure P.Low) : ℕ → ProbabilityMeasure P.Low :=
  fun M => if h : M0 ≤ M then tail M h else diracProba (⟨0,le_rfl,P.d_nonneg⟩ : P.Low)

@[simp] lemma extend_joint_prefix_tail (mu : Measure P.Value) [IsProbabilityMeasure mu]
    (M0 : ℕ) (tail : ∀ M : ℕ, M0 ≤ M → Law (A:=P.Bid) mu) (M : ℕ) (h : M0 ≤ M) :
    P.extend_joint_prefix mu M0 tail M=tail M h := by
  simp only [extend_joint_prefix,dif_pos h]

@[simp] lemma extend_low_prefix_tail (M0 : ℕ)
    (tail : ∀ M : ℕ, M0 ≤ M → ProbabilityMeasure P.Low) (M : ℕ) (h : M0 ≤ M) :
    P.extend_low_prefix M0 tail M=tail M h := by
  simp only [extend_low_prefix,dif_pos h]

theorem retained_low_original_witnesses (c : ℕ → ℕ)
    (muLow : Measure P.Low) [IsProbabilityMeasure muLow] (M0 : ℕ)
    (A : ∀ M : ℕ, M0 ≤ M → P.LowSourceState M (c M) muLow) :
    ∀ M ≥ M0, ∃ W : P.LowSourceState M (c M) muLow,
      P.extend_low_prefix M0 (fun M h => (A M h).bidLaw) M=W.bidLaw := by
  intro M h
  exact ⟨A M h,P.extend_low_prefix_tail M0 _ M h⟩

theorem extended_family_atomless (c : ℕ → ℕ)
    (muLow : Measure P.Low) [IsProbabilityMeasure muLow]
    (mu : Measure P.Value) [IsProbabilityMeasure mu] (M0 : ℕ)
    (A : ∀ M : ℕ, M0 ≤ M → P.LowSourceState M (c M) muLow)
    (E : ∀ (M : ℕ) (h : M0 ≤ M), P.FiniteLawSolution M (c M) (A M h).bidLaw mu) :
    ∀ M ≥ M0, NullSingletonClass
      ((P.extend_joint_prefix mu M0 (fun M h => (E M h).joint) M).1.map
        measurable_snd.aemeasurable : Measure P.Bid) := by
  intro M h
  simpa only [P.extend_joint_prefix_tail mu M0 _ M h] using (E M h).atomless

theorem extended_family_exact_IC (c : ℕ → ℕ)
    (muLow : Measure P.Low) [IsProbabilityMeasure muLow]
    (mu : Measure P.Value) [IsProbabilityMeasure mu] (M0 : ℕ)
    (A : ∀ M : ℕ, M0 ≤ M → P.LowSourceState M (c M) muLow)
    (E : ∀ (M : ℕ) (h : M0 ≤ M), P.FiniteLawSolution M (c M) (A M h).bidLaw mu) :
    let low := P.extend_low_prefix M0 (fun M h => (A M h).bidLaw)
    let pi := P.extend_joint_prefix mu M0 (fun M h => (E M h).joint)
    ∀ M ≥ M0, ∀ᵐ t ∂((pi M).1 : Measure (P.Value×P.Bid)), ∀ b' : P.Bid,
      P.exactUtility (M-1) (c M) (low M) mu (pi M) (t.1,b') ≤
        P.exactUtility (M-1) (c M) (low M) mu (pi M) t := by
  intro low pi M h
  simpa only [low,pi,P.extend_joint_prefix_tail mu M0 _ M h,
    P.extend_low_prefix_tail M0 _ M h] using (E M h).all_bid_IC

end Primitives
end FCAppendix.Affine.Hybrid.Finish01
