import FCAppendix.Affine.Hybrid.Tail03.Moments
import FCAppendix.Affine.Hybrid.Tail03.RelativeMomentRectangle

noncomputable section
namespace FCAppendix.Affine.Hybrid.Tail03
open MeasureTheory Set

lemma ExplicitMomentRectangleInequalities.shrink {p : Center} {rect : Rectangle p}
    {u0 z0 u z : ℝ} (h : ExplicitMomentRectangleInequalities p rect u0 z0)
    (hu : 0<u) (hz : 0<z) (hu0 : u≤u0) (hz0 : z≤z0) :
    ExplicitMomentRectangleInequalities p rect u z := by
  have hmass (G : ProbabilityMeasure ℝ)
      (hm : 1-2*z≤(G : Measure ℝ).real (Icc 1 (1+u))) :
      1-2*z0≤(G : Measure ℝ).real (Icc 1 (1+u0)) := by
    have hs : Icc (1:ℝ) (1+u)⊆Icc 1 (1+u0) :=
      fun b hb => ⟨hb.1,hb.2.trans (add_le_add_right hu0 1)⟩
    exact (show 1-2*z0≤1-2*z by linarith only [hz0]).trans
      (hm.trans (measureReal_mono hs))
  exact ⟨hu,hu0.trans_lt h.u_lt_width,hz,hz0.trans_lt h.zeta_small,
    fun G hs hm => h.denominator G hs (hmass G hm),
    fun G hs hm => h.invariant G hs (hmass G hm)⟩

def SourceRelativeMomentParameters.shrink {p : Center} {lo hi : Fin 2→ℝ}
    (h : SourceRelativeMomentParameters p lo hi) (u z : ℝ)
    (hu : 0<u) (hz : 0<z) (hu0 : u≤h.u) (hz0 : z≤h.zeta) :
    SourceRelativeMomentParameters p lo hi where
  rho := h.rho
  u := u
  zeta := z
  rho_pos := h.rho_pos
  rho_half := h.rho_half
  u_pos := hu
  u_lt_width := hu0.trans_lt h.u_lt_width
  zeta_pos := hz
  zeta_small := hz0.trans_lt h.zeta_small
  moment_error := by
    have hc : 0≤1+2/width p := by have hw:=width_pos p;positivity
    have hh := mul_le_mul_of_nonneg_right hu0 hc
    exact (show 2*z+u*(1+2/width p)≤2*h.zeta+h.u*(1+2/width p) by
      linarith only [hz0,hh]).trans_lt h.moment_error
  coefficient_error := by
    have hc : 0≤1+2/width p := by have hw:=width_pos p;positivity
    have hh := mul_le_mul_of_nonneg_right hu0 hc
    exact (show 2*z+u*(1+2/width p)≤2*h.zeta+h.u*(1+2/width p) by
      linarith only [hz0,hh]).trans_lt h.coefficient_error
  invariant := h.invariant

theorem exists_common_source_moment_parameters (p : Center) (rect : Rectangle p) :
    ∃ h : SourceRelativeMomentParameters p rect.lo rect.hi,
      ExplicitMomentRectangleInequalities p rect h.u h.zeta := by
  obtain ⟨u0,z0,h0⟩ := positive_bulk_forces_rectangle_invariance p rect
  obtain ⟨h⟩ := exists_sourceRelativeMomentParameters p rect.lo rect.hi rect.center_interior
  let u := min u0 h.u
  let z := min z0 h.zeta
  have hu : 0<u := lt_min h0.u_pos h.u_pos
  have hz : 0<z := lt_min h0.zeta_pos h.zeta_pos
  refine ⟨h.shrink u z hu hz (min_le_right _ _) (min_le_right _ _),?_⟩
  exact h0.shrink hu hz (min_le_left _ _) (min_le_left _ _)

end FCAppendix.Affine.Hybrid.Tail03
