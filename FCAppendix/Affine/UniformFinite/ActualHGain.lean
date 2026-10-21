import FCAppendix.Affine.UniformFinite.ActualBoundaryProbability
import FCAppendix.Affine.UniformFinite.ActualPairGain

noncomputable section
namespace FCAppendix.Affine.UniformFinite
open Set MeasureTheory ProbabilityTheory Filter Topology Classical
open scoped BigOperators

namespace ActualBoundary
open ActualAtoms

variable {A : Type*} [MeasurableSpace A]

theorem finite_H_actual_gain_lower (i : Row) (N L : ℕ)
    (hN : N=L+2*Uniform07.capacity (N+2))
    (hroom : L+1< Uniform07.capacity (N+2))
    (G : Uniform05.RestrictedLaw i) (b : Fin N→ℝ)
    (l u S err W B : ℝ) (hu : 0≤ u) (hS : 0≤ S) (hgain : 0≤ S/2-err)
    (Γ : Measure A) [IsFiniteMeasure Γ] (hΓ : Γ univ≠0)
    (θ : Measure ℝ) [IsFiniteMeasure θ] [NullSingletonClass θ]
    (w x z : A→ℝ) (hw : Measurable w) (hx : Measurable x) (hz : Measurable z)
    (hpush : Γ.map x=θ) (hθ : ∀ᵐy∂θ,y≤ u)
    (hbox : ∀ᵐp∂Γ,l≤ x p ∧ x p≤ u ∧ u< z p ∧ 0< z p ∧ S≤ w p-x p ∧
      z p-l≤ err ∧ |w p|≤ W ∧ |x p|≤ B ∧ |z p|≤ B) :
    (Γ.real univ)^2 *
      (PiBinomial.pmf N (Uniform05.t i) L *
        PiBinomial.pmf (2*Uniform07.capacity (N+2)) (1/2) (Uniform07.capacity (N+2)-L-1)) *
      (S/2-err) ≤
    (categoryRowLaw i N).expect (fun kind =>
      if boundaryEvent (Uniform07.capacity (N+2)) L b u kind then
        ∫p : A×ℝ, actualPairGain i G (pairRow kind) (pairFullBids b 0 0)
          (0:Fin (N+2)) (0:Fin (N+1)).succ (w p.1) (x p.1) p.2 (z p.1) ∂Γ.prod θ
      else 0) := by
  let E := boundaryEvent (Uniform07.capacity (N+2)) L b u
  let C := (Γ.real univ)^2*(S/2-err)
  have hC : 0≤ C := mul_nonneg (sq_nonneg _) hgain
  have hpoint (kind : Fin N→ Fin 3) :
      (if E kind then C else 0) ≤
        if E kind then
          ∫p : A×ℝ, actualPairGain i G (pairRow kind) (pairFullBids b 0 0)
            (0:Fin (N+2)) (0:Fin (N+1)).succ (w p.1) (x p.1) p.2 (z p.1) ∂Γ.prod θ
        else 0 := by
    by_cases hk : E kind
    · rw [if_pos hk, if_pos hk]
      exact finite_actualPairGain_lower i G (pairRow kind) (pairFullBids b 0 0)
        (0:Fin (N+2)) (0:Fin (N+1)).succ (Ne.symm (Fin.succ_ne_zero _))
        (pairRow_focal_mem kind) (pairRow_rival_mem kind)
        (boundary_residuals L hN hroom b u kind hk).2 l u S err W B hS
        (boundary_pair_count L hN hroom b u hu kind hk 0 0)
        Γ hΓ θ w x z hw hx hz hpush hθ hbox
    · simp only [if_neg hk, le_refl]
  have hh := (categoryRowLaw i N).expect_mono hpoint
  have he : (categoryRowLaw i N).expect (fun kind=> if E kind then C else 0) =
      (categoryRowLaw i N).prob E*C := by
    calc
      _ = (categoryRowLaw i N).expect (fun kind=>(if E kind then (1:ℝ) else 0)*C) := by
        apply FiniteLaw.expect_congr
        intro kind
        split_ifs <;> simp
      _ = _ := by rw [FiniteLaw.expect_mul_const, ← FiniteLaw.prob_eq_expect]
  rw [he] at hh
  have hp := literal_H_probability i N (Uniform07.capacity (N+2)) L hN b u
  have hs := mul_le_mul_of_nonneg_right hp hC
  change _≤(categoryRowLaw i N).prob E*C at hs
  have hleft : (PiBinomial.pmf N (Uniform05.t i) L *
      PiBinomial.pmf (2*Uniform07.capacity (N+2)) (1/2) (Uniform07.capacity (N+2)-L-1))*C =
      (Γ.real univ)^2 * (PiBinomial.pmf N (Uniform05.t i) L *
        PiBinomial.pmf (2*Uniform07.capacity (N+2)) (1/2) (Uniform07.capacity (N+2)-L-1)) *
          (S/2-err) := by dsimp only [C]; ring
  rw [hleft] at hs
  exact hs.trans hh

end ActualBoundary
end FCAppendix.Affine.UniformFinite
