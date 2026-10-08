import FCAppendix.Finite.PPICentral
import FCAppendix.Finite.EnvelopeIntegral

noncomputable section
namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Filter Set Topology

theorem volume_ae_of_positive_local_density
    (F : Measure ℝ) (f : ℝ → ℝ) (hf : Measurable f)
    (U : Set ℝ) (hU : MeasurableSet U)
    (hF : F.restrict U = (volume.withDensity (fun x => ENNReal.ofReal (f x))).restrict U)
    (hpos : ∀ x ∈ U, 0 < f x) (P : ℝ → Prop) (hP : ∀ᵐ x ∂F, P x) :
    ∀ᵐ x, x ∈ U → P x := by
  have hr := ae_restrict_of_ae hP (s := U)
  rw [hF] at hr
  have hh := (ae_restrict_iff' hU).mp hr
  rw [ae_withDensity_iff hf.ennreal_ofReal] at hh
  filter_upwards [hh] with x hx hxU
  exact hx (ENNReal.ofReal_pos.mpr (hpos x hxU)).ne' hxU

theorem exists_ae_bestResponse_selection_of_local_density
    {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Γ : FiniteGame m n c Seed) (hu : UsersOptimal Γ) (i : Fin m)
    (f : ℝ → ℝ) (hf : Measurable f) (U : Set ℝ) (hU : MeasurableSet U)
    (hF : Γ.F.restrict U = (volume.withDensity (fun x => ENNReal.ofReal (f x))).restrict U)
    (hpos : ∀ x ∈ U, 0 < f x) :
    ∃ sel : ℝ → JointAction n, ∀ᵐ v, v ∈ U → (problem Γ i).BestResponse v (sel v) := by
  classical
  have hP : ∀ᵐ v ∂Γ.F, ∃ act, (problem Γ i).BestResponse v act :=
    (hu i).mono fun _ hv => hv.exists
  have hvol := volume_ae_of_positive_local_density Γ.F f hf U hU hF hpos _ hP
  let sel : ℝ → JointAction n := fun v =>
    if hv : ∃ act, (problem Γ i).BestResponse v act then hv.choose else Interim.abstain n
  refine ⟨sel, ?_⟩
  filter_upwards [hvol] with v hv hvU
  have he := hv hvU
  dsimp only [sel]
  rw [dif_pos he]
  exact he.choose_spec

theorem exists_local_ae_bestResponse_selections
    {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (M C : ℕ → ℕ) (Γ : ∀ k, FiniteGame (M k) n (C k) Seed)
    (i : ∀ k, Fin (M k)) (F : Measure ℝ) (hcommon : ∀ k, (Γ k).F = F)
    (hu : ∀ k, UsersOptimal (Γ k))
    (f : ℝ → ℝ) (hf : Measurable f) (v : ℝ) (U : Set ℝ) (hUn : U ∈ 𝓝 v)
    (hF : F.restrict U = (volume.withDensity (fun x => ENNReal.ofReal (f x))).restrict U)
    (hc : ContinuousAt f v) (hpos : 0 < f v) :
    ∃ d > 0, ∃ sel : ℕ → ℝ → JointAction n,
      ∀ k, ∀ᵐ w, w ∈ Ioo (v - d) (v + d) → (problem (Γ k) (i k)).BestResponse w (sel k w) := by
  have hUevent : ∀ᶠ w in 𝓝 v, w ∈ U := hUn
  have he : ∀ᶠ w in 𝓝 v, w ∈ U ∧ 0 < f w :=
    hUevent.and (hc (eventually_gt_nhds hpos))
  obtain ⟨d, hd, hball⟩ := Metric.eventually_nhds_iff.mp he
  have hinside : Ioo (v - d) (v + d) ⊆ U := by
    intro w hw
    apply (hball _).1
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [hw.1, hw.2]
  have hpositive : ∀ w ∈ Ioo (v - d) (v + d), 0 < f w := by
    intro w hw
    apply (hball _).2
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [hw.1, hw.2]
  have hlocal (k : ℕ) : (Γ k).F.restrict (Ioo (v - d) (v + d)) =
      (volume.withDensity (fun x => ENNReal.ofReal (f x))).restrict (Ioo (v - d) (v + d)) := by
    rw [hcommon k, ← Measure.restrict_restrict_of_subset hinside, hF,
      Measure.restrict_restrict_of_subset hinside]
  choose sel hsel using fun k => exists_ae_bestResponse_selection_of_local_density
    (Γ k) (hu k) (i k) f hf _ measurableSet_Ioo (hlocal k) hpositive
  exact ⟨d, hd, sel, hsel⟩

end FCAppendix.Bayes
