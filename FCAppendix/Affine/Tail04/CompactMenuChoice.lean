import FCAppendix.Affine.Tail04.CompactSelector
import FCAppendix.Affine.Tail04.SourceMenuIdentity
import FCAppendix.Affine.Tail04.EqualPrivateContinuity

noncomputable section
namespace FCAppendix.Affine.Tail04.CompactMenuChoice
open MeasureTheory ProbabilityTheory Set Classical
open OriginalValues SourceMenuIdentity

variable (P : ValueParameters) (ξ U : ℝ) (hU : 1≤ U)

abbrev Parameter := (ℝ×ℝ)×ℝ

def utility (p : Parameter) (b : Icc (1:ℝ) U) : ℝ :=
  menuUtility P ξ p.1.1 p.1.2 p.2 b

lemma continuous_utility : Continuous (fun z : Parameter×Icc (1:ℝ) U=> utility P ξ U z.1 z.2) := by
  unfold utility menuUtility payment served duplicates mixedProbability exposure
  fun_prop (disch := intro z;have hh:=(z.2: Icc (1:ℝ) U).2.1;linarith)

def graph : Set (Parameter×Icc (1:ℝ) U) :=
  {z | ∀b,utility P ξ U z.1 b≤ utility P ξ U z.1 z.2}

lemma isClosed_graph : IsClosed (graph P ξ U) := by
  have he : graph P ξ U=⋂b : Icc (1:ℝ) U,
      {z | utility P ξ U z.1 b≤ utility P ξ U z.1 z.2} := by
    ext z;simp only [graph,mem_setOf_eq,mem_iInter]
  rw [he]
  exact isClosed_iInter fun b=> isClosed_le
    ((continuous_utility P ξ U).comp (continuous_fst.prodMk continuous_const))
    (continuous_utility P ξ U)

include hU in
lemma graph_nonempty (p : Parameter) : ∃b,(p,b)∈graph P ξ U := by
  letI : Nonempty (Icc (1:ℝ) U) := ⟨⟨1,le_rfl,hU⟩⟩
  obtain ⟨b,_,hb⟩ := isCompact_univ.exists_isMaxOn
    (univ_nonempty : (univ : Set (Icc (1:ℝ) U)).Nonempty)
    ((continuous_utility P ξ U).comp (continuous_const.prodMk continuous_id)).continuousOn
  exact ⟨b,fun y=> hb (mem_univ y)⟩

include hU in
theorem exists_measurable_choice : ∃f : Parameter→ Icc (1:ℝ) U,
    Measurable f ∧ ∀p b,utility P ξ U p b≤ utility P ξ U p (f p) := by
  letI : Nonempty (Icc (1:ℝ) U) := ⟨⟨1,le_rfl,hU⟩⟩
  exact CompactSelector.exists_measurable_selector (graph P ξ U)
    (isClosed_graph P ξ U) (graph_nonempty P ξ U hU)

def choice : Parameter→ Icc (1:ℝ) U := (exists_measurable_choice P ξ U hU).choose

lemma measurable_choice : Measurable (choice P ξ U hU) :=
  (exists_measurable_choice P ξ U hU).choose_spec.1

lemma choice_max (p : Parameter) (b : Icc (1:ℝ) U) :
    menuUtility P ξ p.1.1 p.1.2 p.2 b≤
      menuUtility P ξ p.1.1 p.1.2 p.2 (choice P ξ U hU p) :=
  (exists_measurable_choice P ξ U hU).choose_spec.2 p b

theorem continuous_choice_on (V : Set Parameter) (hunique : ∀p∈V,∀a b,
    (p,a)∈graph P ξ U→(p,b)∈graph P ξ U→ a=b) :
    Continuous (fun p : V=> choice P ξ U hU p) := by
  let G : Set (V×Icc (1:ℝ) U) := {z | ((z.1:Parameter),z.2)∈graph P ξ U}
  have hG : IsClosed G := (isClosed_graph P ξ U).preimage
    (continuous_subtype_val.prodMap continuous_id)
  apply EqualPrivateContinuity.continuous_unique_compact_factor G hG id continuous_id
  · intro p
    exact ⟨choice P ξ U hU p,(exists_measurable_choice P ξ U hU).choose_spec.2 p⟩
  · intro p b hb
    exact hunique p p.2 b (choice P ξ U hU p) hb
      ((exists_measurable_choice P ξ U hU).choose_spec.2 p)

end FCAppendix.Affine.Tail04.CompactMenuChoice
