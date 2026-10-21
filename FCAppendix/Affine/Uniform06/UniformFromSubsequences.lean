import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.UniformFromSubsequences

open Set Filter

variable {C : ℕ → Type*}

theorem positive_bounds
    (K : Set ℝ) (F H : (m : ℕ) → C m → ℝ → ℝ)
    (hseq : ∀ (m : ℕ → ℕ), Tendsto m atTop atTop →
      ∀ (E : (n : ℕ) → C (m n)) (z : ℕ → ℝ), (∀ n,z n ∈ K) →
        ∃ φ : ℕ → ℕ,StrictMono φ ∧ ∃ c U V : ℝ,
          0 < c ∧ 0 < U ∧ 0 < V ∧ ∀ᶠ n in atTop,
            c ≤ F (m (φ n)) (E (φ n)) (z (φ n)) ∧
            F (m (φ n)) (E (φ n)) (z (φ n)) ≤ U ∧
            H (m (φ n)) (E (φ n)) (z (φ n)) ≤ V ∧
            0 ≤ H (m (φ n)) (E (φ n)) (z (φ n))) :
    ∃ A : ℕ, ∀ᶠ m in atTop,∀ E : C m,∀ z ∈ K,
      1/((A:ℝ)+1) ≤ F m E z ∧ F m E z ≤ (A:ℝ)+1 ∧
      H m E z ≤ (A:ℝ)+1 ∧ 0 ≤ H m E z := by
  classical
  suffices h : ∃ A M : ℕ,∀ m ≥ M,∀ E : C m,∀ z ∈ K,
      1/((A:ℝ)+1) ≤ F m E z ∧ F m E z ≤ (A:ℝ)+1 ∧
      H m E z ≤ (A:ℝ)+1 ∧ 0 ≤ H m E z by
    obtain ⟨A,M,hM⟩ := h
    exact ⟨A,eventually_atTop.mpr ⟨M,hM⟩⟩
  by_contra h
  have hb (n : ℕ) : ∃ m ≥ n,∃ E : C m,∃ z ∈ K,
      ¬ (1/((n:ℝ)+1) ≤ F m E z ∧ F m E z ≤ (n:ℝ)+1 ∧
        H m E z ≤ (n:ℝ)+1 ∧ 0 ≤ H m E z) := by
    by_contra hn
    push Not at hn
    exact h ⟨n,n,hn⟩
  choose m hm E z hz hbad using hb
  have hmlim : Tendsto m atTop atTop := by
    apply tendsto_atTop.mpr
    intro B
    exact eventually_atTop.mpr ⟨B,fun n hn => hn.trans (hm n)⟩
  obtain ⟨φ,hφ,c,U,V,hc,hU,hV,he⟩ := hseq m hmlim E z hz
  obtain ⟨B,hB⟩ := exists_nat_gt (max (1/c) (max U V))
  have hlarge : ∀ᶠ n in atTop,(B:ℝ) ≤ (φ n:ℝ) := by
    refine eventually_atTop.mpr ⟨B,?_⟩
    intro n hn
    exact_mod_cast hn.trans (hφ.id_le n)
  obtain ⟨n,hn,hBn⟩ := (he.and hlarge).exists
  apply hbad (φ n)
  have hrec : 1/((φ n:ℝ)+1) ≤ c := by
    apply (div_le_iff₀ (by positivity : 0 < (φ n:ℝ)+1)).mpr
    have hbc : 1/c < (B:ℝ) := (le_max_left _ _).trans_lt hB
    have hh := (div_lt_iff₀ hc).mp hbc
    nlinarith
  have hUb : U < (B:ℝ) := (le_max_of_le_right (le_max_left _ _)).trans_lt hB
  have hVb : V < (B:ℝ) := (le_max_of_le_right (le_max_right _ _)).trans_lt hB
  exact ⟨hrec.trans hn.1,hn.2.1.trans (by linarith),
    hn.2.2.1.trans (by linarith),hn.2.2.2⟩

end FCAppendix.Affine.Uniform06.UniformFromSubsequences
