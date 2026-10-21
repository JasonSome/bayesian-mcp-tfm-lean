import FCAppendix.Existence.R01PayOnceClippingError
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section
namespace FCAppendix.Existence.PayOnceBounded
open Set Filter Topology MeasureTheory ProbabilityTheory
open FCAppendix.Existence.Distributional
attribute [local instance] Classical.propDecidable

section ClosedMass
variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
  [TopologicalSpace.MetrizableSpace X] [BorelSpace X]

theorem eventually_closed_mass_lt (ν : ℕ→ProbabilityMeasure X) (ν₀ : ProbabilityMeasure X)
    (hν : Tendsto ν atTop (𝓝 ν₀)) (C : Set X) (hC : IsClosed C)
    (r : ℝ) (hr : (ν₀ : Measure X).real C<r) :
    ∀ᶠj in atTop,(ν j : Measure X).real C<r := by
  by_cases hr1 : 1<r
  · exact Filter.Eventually.of_forall (fun j=>
      (show (ν j : Measure X).real C≤1 by
        calc
          _≤(ν j : Measure X).real univ := measureReal_mono (subset_univ C)
          _=1 := by simp).trans_lt hr1)
  · have h1r : 0≤1-r := sub_nonneg.mpr (le_of_not_gt hr1)
    have he := eventually_open_mass_gt ν ν₀ hν Cᶜ hC.isOpen_compl (1-r) h1r
      (by rw [probReal_compl_eq_one_sub hC.measurableSet]; linarith)
    filter_upwards [he] with j hj
    rw [probReal_compl_eq_one_sub hC.measurableSet] at hj
    linarith
end ClosedMass

theorem smallActive_mass_tendsto_zero {W : ℝ}
    (π : ProbabilityMeasure (Value W × FloorAction 0 W))
    (hzero : (π : Measure (Value W × FloorAction 0 W))
      {z|present z.2=true ∧ bid z.2=0}=0)
    (δ : ℕ→ℝ) (hδ0 : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun j=>(π : Measure (Value W × FloorAction 0 W)).real (smallActive (δ j)))
      atTop (𝓝 0) := by
  let F : ℕ→(Value W × FloorAction 0 W)→ℝ := fun j z=>if z∈smallActive (δ j) then 1 else 0
  have hmeas (j:ℕ) : AEStronglyMeasurable (F j) (π : Measure (Value W × FloorAction 0 W)) := by
    exact (measurable_const.ite (isClosed_smallActive (δ j)).measurableSet measurable_const).aestronglyMeasurable
  have hlim : ∀ᵐz ∂(π : Measure (Value W × FloorAction 0 W)),
      Tendsto (fun j=>F j z) atTop (𝓝 (0:ℝ)) := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hzero] with z hz
    by_cases hp : present z.2=true
    · have hb0 : 0≤bid z.2 := by cases ha:z.2 with
        | inl u => exact le_rfl
        | inr b => exact b.2.1
      have hb : 0<bid z.2 := lt_of_le_of_ne hb0 (Ne.symm (fun h=>hz ⟨hp,h⟩))
      have he : ∀ᶠj in atTop,F j z=0 := by
        filter_upwards [hδ0.eventually (Iio_mem_nhds hb)] with j hj
        have hn : z∉smallActive (δ j) := fun hm=>not_le_of_gt hj hm.2
        simp [F,hn]
      exact tendsto_const_nhds.congr' (he.mono (fun _ hj=>hj.symm))
    · have he : ∀j,F j z=0 := fun j=>by
        have hn : z∉smallActive (δ j) := fun hm=>hp hm.1
        simp [F,hn]
      simpa only [he] using (tendsto_const_nhds (x:=(0:ℝ)) : Tendsto (fun _ : ℕ=>(0:ℝ)) atTop (𝓝 0))
  have ht := tendsto_integral_of_dominated_convergence (fun _=>1) hmeas (integrable_const (1:ℝ))
    (fun j=>Filter.Eventually.of_forall (fun z=>by
      change ‖if z∈smallActive (δ j) then (1:ℝ) else 0‖≤1
      split_ifs <;> norm_num)) hlim
  have hi (j:ℕ) : (∫z,F j z ∂(π : Measure (Value W × FloorAction 0 W)))=
      (π : Measure (Value W × FloorAction 0 W)).real (smallActive (δ j)) := by
    convert integral_indicator_one (μ:=(π : Measure (Value W × FloorAction 0 W)))
      (isClosed_smallActive (δ j)).measurableSet using 1
    all_goals rfl
  simpa only [hi,integral_zero] using ht

theorem abs_expected_profile_clipping_error {W : ℝ} (m n c : ℕ) (hn : 2≤n)
    (δ : ℝ) (hδ : 0<δ) (hδW : δ≤W)
    (π : ProbabilityMeasure (Value W × FloorAction 0 W)) (i : Fin m) :
    |(∫x,clippedProfilePayoff m n c δ hδW x i ∂(rowLaw m π : Measure (Fin m→Value W × FloorAction 0 W)))-
      (∫x,positiveProfilePayoff m n c x i ∂(rowLaw m π : Measure (Fin m→Value W × FloorAction 0 W)))| ≤
      (2*W)*m*(π : Measure (Value W × FloorAction 0 W)).real (smallActive δ) := by
  have hiP : Integrable (fun x=>positiveProfilePayoff m n c x i) (rowLaw m π : Measure (Fin m→Value W × FloorAction 0 W)) := by
    apply Integrable.of_bound (measurable_positiveProfilePayoff (W:=W) m n c hn i).aestronglyMeasurable W
    exact Filter.Eventually.of_forall (fun x=>by simpa only [Real.norm_eq_abs] using
      (positiveProfilePayoff_abs_le m n c hn (hδ.le.trans hδW) x i))
  have hiC : Integrable (fun x=>clippedProfilePayoff m n c δ hδW x i)
      (rowLaw m π : Measure (Fin m→Value W × FloorAction 0 W)) :=
    (ContinuousMap.equivBoundedOfCompact _ _
      ⟨_,continuous_clippedProfilePayoff m n c hn δ hδ hδW i⟩).integrable _
  rw [← integral_sub hiC hiP]
  have hh := norm_integral_le_integral_norm (μ:=(rowLaw m π : Measure (Fin m→Value W × FloorAction 0 W)))
    (fun x=>clippedProfilePayoff m n c δ hδW x i-positiveProfilePayoff m n c x i)
  have hnrm : |∫x,clippedProfilePayoff m n c δ hδW x i-positiveProfilePayoff m n c x i
      ∂(rowLaw m π : Measure (Fin m→Value W × FloorAction 0 W))| ≤
      ∫x,|clippedProfilePayoff m n c δ hδW x i-positiveProfilePayoff m n c x i|
        ∂(rowLaw m π : Measure (Fin m→Value W × FloorAction 0 W)) := by
    simpa only [Real.norm_eq_abs] using hh
  exact hnrm.trans (integral_profile_clipping_error_bound m n c hn δ hδ hδW π i)

end FCAppendix.Existence.PayOnceBounded
