import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.CompactUniformSequence

open Set Filter Topology
variable {C : ℕ → Type*}

theorem eventually_all_of_good_subsequence
    (K : Set ℝ) (P : (m : ℕ) → C m → ℝ → Prop)
    (hseq : ∀ (m : ℕ → ℕ),Tendsto m atTop atTop →
      ∀ (E : ∀ n,C (m n)) (b : ℕ → ℝ),(∀ n,b n ∈ K) →
        ∃ φ : ℕ → ℕ,StrictMono φ ∧
          ∀ᶠ n in atTop,P (m (φ n)) (E (φ n)) (b (φ n))) :
    ∀ᶠ m in atTop,∀ E : C m,∀ b ∈ K,P m E b := by
  classical
  by_contra hnot
  have hbad (n : ℕ) : ∃ m ≥ n,∃ E : C m,∃ b ∈ K,¬ P m E b := by
    by_contra hn
    push Not at hn
    exact hnot (eventually_atTop.mpr ⟨n,hn⟩)
  choose m hm E b hb hfail using hbad
  have hmlim : Tendsto m atTop atTop := by
    apply tendsto_atTop.mpr
    intro M
    exact eventually_atTop.mpr ⟨M,fun n hn => hn.trans (hm n)⟩
  obtain ⟨φ,hφ,hgood⟩ := hseq m hmlim E b hb
  obtain ⟨n,hn⟩ := hgood.exists
  exact hfail (φ n) hn

theorem uniformly_vanishes_of_good_subsequence
    (K : Set ℝ) (P : (m : ℕ) → C m → ℝ → Prop)
    (err : (m : ℕ) → C m → ℝ → ℝ)
    (hseq : ∀ (m : ℕ → ℕ),Tendsto m atTop atTop →
      ∀ (E : ∀ n,C (m n)) (b : ℕ → ℝ),(∀ n,b n ∈ K) →
        ∃ φ : ℕ → ℕ,StrictMono φ ∧
          (∀ᶠ n in atTop,P (m (φ n)) (E (φ n)) (b (φ n))) ∧
          Tendsto (fun n => err (m (φ n)) (E (φ n)) (b (φ n))) atTop (𝓝 0)) :
    ∀ ε > (0:ℝ),∀ᶠ m in atTop,∀ E : C m,∀ b ∈ K,
      P m E b ∧ |err m E b| < ε := by
  intro ε hε
  apply eventually_all_of_good_subsequence K
    (fun m E b => P m E b ∧ |err m E b| < ε)
  intro m hm E b hb
  obtain ⟨φ,hφ,hP,he⟩ := hseq m hm E b hb
  refine ⟨φ,hφ,?_⟩
  have he' : ∀ᶠ n in atTop,|err (m (φ n)) (E (φ n)) (b (φ n))| < ε := by
    have hAbs : Tendsto (fun n => |err (m (φ n)) (E (φ n)) (b (φ n))|)
        atTop (𝓝 0) := by simpa only [abs_zero] using he.abs
    exact hAbs.eventually_lt_const hε
  exact hP.and he'

end FCAppendix.Affine.Uniform06.CompactUniformSequence
