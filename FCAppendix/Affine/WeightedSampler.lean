import FCAppendix.Affine.WeightedSampling

noncomputable section
namespace FCAppendix.Affine.WeightedSampling
open Set MeasureTheory
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
omit [DecidableEq ι] [Nonempty ι] in
lemma continuous_totalWeight : Continuous (totalWeight : Weights ι → ℝ) := by
  unfold totalWeight
  fun_prop

omit [Nonempty ι] in
lemma continuous_remainingWeight (S : Finset ι) :
    Continuous (fun w : Weights ι => remainingWeight w S) := by
  classical
  unfold remainingWeight
  apply continuous_finsetSum
  intro i _
  by_cases hi : i ∈ S
  · simp only [hi, if_true]
    exact continuous_const
  · simp only [hi, if_false]
    exact (continuous_apply i).comp continuous_subtype_val

lemma measurable_oneDraw_mass (S : Finset ι) (i : ι) :
    Measurable (fun w : Weights ι => (oneDraw w S).mass i) := by
  classical
  have hpos : MeasurableSet {w : Weights ι | 0 < remainingWeight w S} :=
    (isOpen_lt continuous_const (continuous_remainingWeight S)).measurableSet
  have hnum : Measurable (fun w : Weights ι => if i ∈ S then 0 else w.1 i) := by
    by_cases hi : i ∈ S
    · simp only [hi, if_true]
      exact measurable_const
    · simp only [hi, if_false]
      exact ((continuous_apply i).comp continuous_subtype_val).measurable
  have he : (fun w : Weights ι => (oneDraw w S).mass i)=
      (fun w => if 0<remainingWeight w S then
        (if i∈S then 0 else w.1 i)/remainingWeight w S
      else (FiniteLaw.dirac (Classical.choice ‹Nonempty ι›)).mass i) := by
    funext w
    by_cases h : 0<remainingWeight w S
    · rw [if_pos h,oneDraw_mass w S h]
    · simp [oneDraw,h]
  rw [he]
  exact Measurable.ite hpos (hnum.div (continuous_remainingWeight S).measurable)
    measurable_const

lemma measurable_pathLaw_mass (n : ℕ) (S : Finset ι) (p : Path ι n) :
    Measurable (fun w : Weights ι => (pathLaw w n S).mass p) := by
  induction n generalizing S with
  | zero => exact measurable_const
  | succ n ih =>
    change Measurable (fun w : Weights ι =>
      (oneDraw w S).mass p.1 * (pathLaw w n (insert p.1 S)).mass p.2)
    exact (measurable_oneDraw_mass S p.1).mul (ih (insert p.1 S) p.2)

instance pathNonempty (n : ℕ) : Nonempty (Path ι n) := by
  induction n with
  | zero => exact ⟨PUnit.unit⟩
  | succ n ih =>
    letI : Nonempty (Path ι n) := ih
    exact inferInstanceAs (Nonempty (ι × Path ι n))

instance pathMeasurableSpace (n : ℕ) : MeasurableSpace (Path ι n) := ⊤

instance pathMeasurableSingletonClass (n : ℕ) :
    MeasurableSingletonClass (Path ι n) := ⟨fun _ => trivial⟩

instance pathStandardBorelSpace (n : ℕ) : StandardBorelSpace (Path ι n) := by
  infer_instance

theorem exists_weighted_sampler (n : ℕ) (S : Finset ι) :
    ∃ f : Weights ι → unitInterval → Path ι n,
      Measurable (Function.uncurry f) ∧
      ∀ w, volume.map (f w) = FiniteLaw.probabilityMeasure (pathLaw w n S) :=
  FiniteLaw.exists_measurable_sampler (fun w => pathLaw w n S)
    (measurable_pathLaw_mass n S)

theorem exists_weighted_sampler_on {X : Type*} [MeasurableSpace X]
    (w : X → Weights ι) (hw : Measurable w) (n : ℕ) (S : Finset ι) :
    ∃ f : X → unitInterval → Path ι n,
      Measurable (Function.uncurry f) ∧
      ∀ x, volume.map (f x) = FiniteLaw.probabilityMeasure (pathLaw (w x) n S) := by
  obtain ⟨f,hf,hlaw⟩ := exists_weighted_sampler (ι := ι) n S
  refine ⟨fun x u => f (w x) u, ?_, fun x => hlaw (w x)⟩
  exact hf.comp ((hw.comp measurable_fst).prodMk measurable_snd)

end FCAppendix.Affine.WeightedSampling
