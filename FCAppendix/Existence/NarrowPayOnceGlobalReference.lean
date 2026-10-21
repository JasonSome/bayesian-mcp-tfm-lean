import FCAppendix.Existence.NarrowPayOnceReference
import Mathlib.Analysis.Convex.Deriv

noncomputable section
namespace FCAppendix.Existence.NarrowPayOnce
open Set Filter Topology CommonList PayOnce PayOnce.OwnImpact

theorem hasDerivAt_success (n : ℕ) (p : ℝ) :
    HasDerivAt (success n) ((n:ℝ)*(1-p)^(n-1)) p := by
  convert (((hasDerivAt_id p).const_sub 1).pow n).const_sub 1 using 1 <;>
    first | rfl | (simp only [id_eq]; ring)

lemma concave_supporting_line {f : ℝ→ℝ} (hf : ConcaveOn ℝ (Icc (0:ℝ) 1) f)
    {ρ p d : ℝ} (hρ : ρ∈Icc (0:ℝ) 1) (hp : p∈Icc (0:ℝ) 1)
    (hd : HasDerivAt f d ρ) : f p≤f ρ+d*(p-ρ) := by
  rcases lt_trichotomy p ρ with hl|he|hr
  · have hh:=hf.le_slope_of_hasDerivAt hp hρ hl hd
    rw [slope_def_field] at hh
    have hmul: d*(ρ-p)≤f ρ-f p := (le_div_iff₀ (sub_pos.mpr hl)).mp hh
    nlinarith
  · subst p
    simp
  · have hh:=hf.slope_le_of_hasDerivAt hρ hp hr hd
    rw [slope_def_field] at hh
    have hmul: f p-f ρ≤d*(p-ρ) := (div_le_iff₀ (sub_pos.mpr hr)).mp hh
    linarith

theorem success_strictConcaveOn {n : ℕ} (hn : 2≤n) :
    StrictConcaveOn ℝ (Icc (0:ℝ) 1) (success n) := by
  apply StrictAntiOn.strictConcaveOn_of_deriv (convex_Icc _ _) (continuous_success n).continuousOn
  intro x hx y hy hxy
  rw [interior_Icc] at hx hy
  rw [(hasDerivAt_success n x).deriv,(hasDerivAt_success n y).deriv]
  apply mul_lt_mul_of_pos_left _ (Nat.cast_pos.mpr (by omega : 0<n))
  exact pow_lt_pow_left₀ (by linarith) (by linarith [hy.2]) (by omega : n-1≠0)

def successTangentGap (n : ℕ) (ρ p : ℝ) : ℝ :=
  success n ρ-success n p+(n:ℝ)*(1-ρ)^(n-1)*(p-ρ)

theorem successTangentGap_pos {n : ℕ} (hn : 2≤n) {ρ p : ℝ}
    (hρ : ρ∈Icc (0:ℝ) 1) (hp : p∈Icc (0:ℝ) 1) (hne : p≠ρ) :
    0<successTangentGap n ρ p := by
  have hf:=success_strictConcaveOn hn
  rcases lt_or_gt_of_ne hne with hl|hr
  · have hh:=hf.lt_slope_of_hasDerivAt hp hρ hl (hasDerivAt_success n ρ)
    rw [slope_def_field] at hh
    have hmul := (lt_div_iff₀ (sub_pos.mpr hl)).mp hh
    dsimp [successTangentGap]
    nlinarith
  · have hh:=hf.slope_lt_of_hasDerivAt hρ hp hr (hasDerivAt_success n ρ)
    rw [slope_def_field] at hh
    have hmul := (div_lt_iff₀ (sub_pos.mpr hr)).mp hh
    dsimp [successTangentGap]
    linarith

theorem continuous_successTangentGap (n : ℕ) :
    Continuous (fun x : ℝ×ℝ=>successTangentGap n x.1 x.2) := by
  unfold successTangentGap success
  fun_prop

theorem exists_uniform_success_gap {n : ℕ} (hn : 2≤n) {lo hi α : ℝ}
    (hlo : 0≤lo) (hhi : hi≤1) (hα : 0<α) :
    ∃γ : ℝ,0<γ ∧ ∀ρ∈Icc lo hi,∀p∈Icc (0:ℝ) 1,
      α≤|p-ρ| → γ ≤ successTangentGap n ρ p := by
  let K : Set (ℝ×ℝ):=(Icc lo hi ×ˢ Icc (0:ℝ) 1)∩{x|α≤|x.2-x.1|}
  have hK : IsCompact K := (isCompact_Icc.prod isCompact_Icc).inter_right
    (isClosed_le continuous_const ((continuous_snd.sub continuous_fst).abs))
  by_cases hne : K.Nonempty
  · obtain ⟨x,hx,hmin⟩:=hK.exists_isMinOn hne (continuous_successTangentGap n).continuousOn
    have hxp : x.2≠x.1 := by
      intro he
      have hh:=hx.2
      simp [he] at hh
      linarith
    have hpos:=successTangentGap_pos hn ⟨hlo.trans hx.1.1.1,hx.1.1.2.trans hhi⟩ hx.1.2 hxp
    refine ⟨_,hpos,?_⟩
    intro ρ hρ p hp ha
    exact hmin (show (ρ,p)∈K from ⟨⟨hρ,hp⟩,ha⟩)
  · refine ⟨1,by norm_num,?_⟩
    intro ρ hρ p hp ha
    exact False.elim (hne ⟨(ρ,p),⟨⟨hρ,hp⟩,ha⟩⟩)

theorem reference_gap_ge_success_gap {n : ℕ} (hn : 2≤n) {R c w : ℝ}
    (hR : 0<R) (hc : 1≤c) (hcR : c≤R) (hw : 0<w)
    {p : ℝ} (hp : p∈Icc (0:ℝ) 1) :
    w*successTangentGap n (density R c) p≤
      referenceUtility n R c w (referenceBid n R c w) (density R c)-
      referenceUtility n R c w (referenceBid n R c w) p := by
  let B:=referenceBid n R c w
  let F:=referenceUtility n R c 0 B
  have hB:0<B := (referenceBid_pos_lt hn hR hc hcR hw).1
  have hρ:=density_bounds hR hc hcR
  have hd (x : ℝ) : HasDerivAt F (referenceScore n R c 0 B x) x :=
    hasDerivAt_referenceUtility n R c 0 B x
  have hanti : AntitoneOn (deriv F) (interior (Icc (0:ℝ) 1)) := by
    intro x hx y hy hxy
    rw [(hd x).deriv,(hd y).deriv]
    exact (referenceScore_strictAntiOn hn hR hc hcR (by norm_num : (0:ℝ)≤0) hB).antitoneOn
      (interior_subset hx) (interior_subset hy) hxy
  have hconcave:ConcaveOn ℝ (Icc (0:ℝ) 1) F :=
    hanti.concaveOn_of_deriv (convex_Icc _ _)
      ((continuous_iff_continuousAt.mpr fun x=>(hd x).continuousAt).continuousOn)
      (fun x _=>(hd x).differentiableAt.differentiableWithinAt)
  have hsupport:=concave_supporting_line hconcave ⟨hρ.1.le,hρ.2.le⟩ hp (hd (density R c))
  have hz:=referenceScore_at_density hn (w:=w) hR hc hcR
  have hzmul:=congrArg (fun x : ℝ=>x*(p-density R c)) hz
  dsimp [F,B,referenceUtility,referenceScore,successTangentGap] at hsupport hzmul ⊢
  nlinarith only [hsupport,hzmul]

end FCAppendix.Existence.NarrowPayOnce
