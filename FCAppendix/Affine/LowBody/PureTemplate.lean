import FCAppendix.Affine.LowBody.NoisyPurePayoff

noncomputable section
namespace FCAppendix.Affine.LowBody
open MeasureTheory Set
open scoped BigOperators

variable (ι : Type*) [Fintype ι] [DecidableEq ι]
structure PureTemplate where
  support : Finset ι
  residual₀ : ℕ
  residual₁ : ℕ

namespace PureTemplate
variable {ι}

def Feasible (T : PureTemplate ι) (P : Finset ι × Finset ι) : Prop :=
  P.1.card≤T.residual₀ ∧ P.1⊆T.support ∧ P.2.card≤T.residual₁ ∧ P.2⊆T.support

abbrev Candidate (T : PureTemplate ι) := {P : Finset ι × Finset ι // T.Feasible P}

noncomputable instance candidateFintype (T : PureTemplate ι) : Fintype T.Candidate := Fintype.ofFinite _
instance candidateNonempty (T : PureTemplate ι) : Nonempty T.Candidate :=
  ⟨⟨(∅,∅),by simp [Feasible]⟩⟩

def selection (T : PureTemplate ι) (κ : ℝ) (b : ι→ℝ) : Finset ι × Finset ι :=
  (FiniteSelector.select (fun P : T.Candidate=>CompleteInformation.potential κ b P.1.1 P.1.2)).val

theorem selection_feasible (T : PureTemplate ι) (κ : ℝ) (b : ι→ℝ) :
    T.Feasible (T.selection κ b) :=
  (FiniteSelector.select (fun P : T.Candidate=>CompleteInformation.potential κ b P.1.1 P.1.2)).property

theorem selection_max (T : PureTemplate ι) (κ : ℝ) (b : ι→ℝ)
    (P : Finset ι × Finset ι) (hP : T.Feasible P) :
    CompleteInformation.potential κ b P.1 P.2≤
      CompleteInformation.potential κ b (T.selection κ b).1 (T.selection κ b).2 :=
  FiniteSelector.select_max
    (fun Q : T.Candidate=>CompleteInformation.potential κ b Q.1.1 Q.1.2) (⟨P,hP⟩ : T.Candidate)

theorem selection_nash (T : PureTemplate ι) (κ : ℝ) (b : ι→ℝ) :
    (∀S : Finset ι,S.card≤T.residual₀→S⊆T.support→
      CompleteInformation.revenue κ b S (T.selection κ b).2≤
        CompleteInformation.revenue κ b (T.selection κ b).1 (T.selection κ b).2) ∧
    (∀S : Finset ι,S.card≤T.residual₁→S⊆T.support→
      CompleteInformation.revenue κ b S (T.selection κ b).1≤
        CompleteInformation.revenue κ b (T.selection κ b).2 (T.selection κ b).1) := by
  have hf:=T.selection_feasible κ b
  constructor
  · intro S hS hsub
    have hh:=T.selection_max κ b (S,(T.selection κ b).2) ⟨hS,hsub,hf.2.2.1,hf.2.2.2⟩
    rw [CompleteInformation.potential_eq_revenue_add,CompleteInformation.potential_eq_revenue_add] at hh
    exact le_of_add_le_add_right hh
  · intro S hS hsub
    have hh:=T.selection_max κ b ((T.selection κ b).1,S) ⟨hf.1,hf.2.1,hS,hsub⟩
    rw [CompleteInformation.potential_comm κ b (T.selection κ b).1 S,
      CompleteInformation.potential_comm κ b (T.selection κ b).1 (T.selection κ b).2,
      CompleteInformation.potential_eq_revenue_add,CompleteInformation.potential_eq_revenue_add] at hh
    exact le_of_add_le_add_right hh

def noisyUserPayoff (T : PureTemplate ι) (κ ε : ℝ) (i : ι) (t : ℝ×(ι→ℝ)) (z : ℝ) : ℝ :=
  purePayoff κ t.1 (noisyFocal i ε t.2 z) (T.selection κ (noisyFocal i ε t.2 z)) i

theorem noisyUserPayoff_eq (T : PureTemplate ι) (κ ε : ℝ) (i : ι)
    (t : ℝ×(ι→ℝ)) (z : ℝ) :
    T.noisyUserPayoff κ ε i t z=
      pureNoisyPayoff (fun P : T.Candidate=>P.val) κ ε i t z := rfl

theorem continuous_parameter_payoff (T : PureTemplate ι)
    {κ ε : ℝ} (hκ : 0<κ) (hε : ε≠0) (i : ι) :
    Continuous (fun t : ℝ×Ioi (0:ℝ)×(ι→ℝ)=>
      ∫z,T.noisyUserPayoff κ ε i (parameterBids i (t.1,t.2.1.1,t.2.2)) z ∂uniformNoise) :=
  continuous_parameterPurePayoff_positive (fun P : T.Candidate=>P.val) hκ hε i

end PureTemplate
end FCAppendix.Affine.LowBody
