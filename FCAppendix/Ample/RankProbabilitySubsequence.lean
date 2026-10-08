import FCAppendix.Ample.DownstreamNormalizationCore

noncomputable section
namespace FCAppendix.Ample.DownstreamNormalizationCore
open MeasureTheory Filter Topology

theorem not_probZero_iff_bad_subsequence
    {Ω : ℕ → Type*} [∀ t, MeasurableSpace (Ω t)]
    (μ : (t : ℕ) → Measure (Ω t)) (X : (t : ℕ) → Ω t → ℝ) :
    ¬ ProbZero μ X ↔
      ∃ ε > 0, ∃ η > 0, ∃ phi : ℕ → ℕ, StrictMono phi ∧
        ∀ t, ENNReal.ofReal η ≤ μ (phi t) {x | ε < |X (phi t) x|} := by
  classical
  constructor
  · intro h
    obtain ⟨ε, hεbad⟩ := not_forall.mp h
    obtain ⟨hε, hεbad⟩ := Classical.not_imp.mp hεbad
    obtain ⟨η, hηbad⟩ := not_forall.mp hεbad
    obtain ⟨hη, hnot⟩ := Classical.not_imp.mp hηbad
    have hfreq' : ∃ᶠ t in atTop,
        ¬ μ t {x | ε < |X t x|} < ENNReal.ofReal η := by
      simpa only [Filter.Frequently, not_not] using hnot
    have hfreq : ∃ᶠ t in atTop,
        ENNReal.ofReal η ≤ μ t {x | ε < |X t x|} :=
      hfreq'.mono (fun _ ht => le_of_not_gt ht)
    obtain ⟨phi, hphi, hbad⟩ := extraction_of_frequently_atTop hfreq
    exact ⟨ε, hε, η, hη, phi, hphi, hbad⟩
  · rintro ⟨ε, hε, η, hη, phi, hphi, hbad⟩ h
    have he := hphi.tendsto_atTop.eventually (h ε hε η hη)
    obtain ⟨t, ht⟩ := he.exists
    exact (not_lt_of_ge (hbad t)) ht

theorem probZero_subsequence_principle
    {Ω : ℕ → Type*} [∀ t, MeasurableSpace (Ω t)]
    (μ : (t : ℕ) → Measure (Ω t)) (X : (t : ℕ) → Ω t → ℝ)
    (h : ∀ phi : ℕ → ℕ, StrictMono phi →
      ∃ psi : ℕ → ℕ, StrictMono psi ∧
        ProbZero (fun t => μ (phi (psi t))) (fun t => X (phi (psi t)))) :
    ProbZero μ X := by
  classical
  by_contra hnot
  obtain ⟨ε, hε, η, hη, phi, hphi, hbad⟩ :=
    (not_probZero_iff_bad_subsequence μ X).mp hnot
  obtain ⟨psi, _hpsi, hgood⟩ := h phi hphi
  obtain ⟨t, ht⟩ := (hgood ε hε η hη).exists
  exact (not_lt_of_ge (hbad (psi t))) ht

theorem probZero_along
    {Ω : ℕ → Type*} [∀ t, MeasurableSpace (Ω t)]
    {μ : (t : ℕ) → Measure (Ω t)} {X : (t : ℕ) → Ω t → ℝ}
    (h : ProbZero μ X) (phi : ℕ → ℕ) (hphi : Tendsto phi atTop atTop) :
    ProbZero (fun t => μ (phi t)) (fun t => X (phi t)) := by
  intro ε hε η hη
  exact hphi.eventually (h ε hε η hη)

end FCAppendix.Ample.DownstreamNormalizationCore
