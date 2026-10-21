import FCAppendix.Affine.Hybrid.Tail03.Taylor

noncomputable section
namespace FCAppendix.Affine.Hybrid.Tail03
open Set Filter Topology

def marginalCost (p : Center) (lam : Fin 2 → ℝ) (b : ℝ) : ℝ :=
  payment1 p lam b/served1 p lam b

lemma marginalCost_hasDerivAt (p : Center) (rect : Rectangle p)
    (h : RectangleAnalyticCertificate p rect) (lam : Fin 2 → ℝ)
    (hlam : lam∈rect.box) {b : ℝ} (hb : b∈Ico (1:ℝ) (B p)) :
    HasDerivAt (marginalCost p lam)
      ((payment2 p lam b*served1 p lam b-payment1 p lam b*served2 p lam b)/
        (served1 p lam b)^2) b := by
  exact (payment1_hasDerivAt p lam (ne_of_gt (by linarith [hb.1]))).div
    (served1_hasDerivAt p lam (ne_of_gt (by linarith [hb.1])))
    (h.derivative.served_pos lam hlam b hb).ne'

theorem marginalCost_strictMonoOn (p : Center) (rect : Rectangle p)
    (h : RectangleAnalyticCertificate p rect) (lam : Fin 2 → ℝ)
    (hlam : lam∈rect.box) : StrictMonoOn (marginalCost p lam) (Ico (1:ℝ) (B p)) := by
  intro a ha b hb hab
  let slope := fun x =>
    (payment2 p lam x*served1 p lam x-payment1 p lam x*served2 p lam x)/(served1 p lam x)^2
  obtain ⟨z,hz,hzd⟩ := exists_hasDerivAt_eq_slope (marginalCost p lam) slope hab
    (fun x hx => (marginalCost_hasDerivAt p rect h lam hlam
      ⟨ha.1.trans hx.1,hx.2.trans_lt hb.2⟩).continuousAt.continuousWithinAt)
    (fun x hx => marginalCost_hasDerivAt p rect h lam hlam
      ⟨ha.1.trans hx.1.le,hx.2.le.trans_lt hb.2⟩)
  have hzK : z∈Ico (1:ℝ) (B p) := ⟨ha.1.trans hz.1.le,hz.2.le.trans_lt hb.2⟩
  have hp : 0< slope z := div_pos
    (h.derivative.determinant_pos lam hlam z ⟨hzK.1,hzK.2.le⟩)
    (sq_pos_of_pos (h.derivative.served_pos lam hlam z hzK))
  rw [hzd] at hp
  have hdiff := (div_pos_iff_of_pos_right (sub_pos.mpr hab)).mp hp
  linarith

theorem marginalCost_tendsto_atTop (p : Center) (rect : Rectangle p)
    (h : RectangleAnalyticCertificate p rect) (lam : Fin 2 → ℝ)
    (hlam : lam∈rect.box) :
    Tendsto (marginalCost p lam) (𝓝[<] (B p)) atTop := by
  have hB0 : B p≠0 := ne_of_gt ((by norm_num : (0:ℝ)<1).trans (B_gt_one p))
  have hc := derivative_continuity p lam (B p) hB0
  have hm : ContinuousAt (fun b : ℝ => (lam,b)) (B p) := by fun_prop
  have hs : Tendsto (served1 p lam) (𝓝 (B p)) (𝓝 0) := by
    simpa only [Function.comp_def,(derivatives_at_B p lam).1] using (hc.1.comp_of_eq hm rfl).tendsto
  have ht : Tendsto (payment1 p lam) (𝓝 (B p)) (𝓝 1) := by
    simpa only [Function.comp_def,(derivatives_at_B p lam).2] using (hc.2.2.1.comp_of_eq hm rfl).tendsto
  apply tendsto_atTop.2
  intro K
  have heps : 0<1/(2*(|K|+1)) := by positivity
  have hsmall : ∀ᶠb in 𝓝[<] (B p),served1 p lam b<1/(2*(|K|+1)) := ((tendsto_order.1 hs).2 (1/(2*(|K|+1))) heps).filter_mono nhdsWithin_le_nhds
  have hlarge : ∀ᶠb in 𝓝[<] (B p),(1/2:ℝ)<payment1 p lam b := ((tendsto_order.1 ht).1 (1/2) (by norm_num)).filter_mono nhdsWithin_le_nhds
  have hleft : ∀ᶠ b in 𝓝[<] (B p),1< b :=
    (eventually_gt_nhds (B_gt_one p)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hsmall,hlarge,hleft,self_mem_nhdsWithin] with b hs ht hleft hright
  have hpos := h.derivative.served_pos lam hlam b ⟨hleft.le,hright⟩
  unfold marginalCost
  apply (le_div_iff₀ hpos).2
  have hprod := (lt_div_iff₀ (show 0<2*(|K|+1) by positivity)).mp hs
  have hK := le_abs_self K
  have hbound := mul_le_mul_of_nonneg_right hK hpos.le
  nlinarith

def canonicalTailResponse (p : Center) (rect : Rectangle p)
    (d : BoundaryTaylorData p rect) (lam : Fin 2 → ℝ) (v : ℝ) : ℝ :=
  d.response lam (max d.V0 v)

lemma canonicalTailResponse_eq (p : Center) (rect : Rectangle p)
    (d : BoundaryTaylorData p rect) (lam : Fin 2 → ℝ) {v : ℝ} (hv : d.V0≤ v) :
    canonicalTailResponse p rect d lam v=d.response lam v := by
  simp [canonicalTailResponse,max_eq_right hv]

theorem canonicalTailResponse_monotone (p : Center) (rect : Rectangle p)
    (h : RectangleAnalyticCertificate p rect) (d : BoundaryTaylorData p rect)
    (lam : Fin 2 → ℝ) (hlam : lam∈rect.box) :
    Monotone (canonicalTailResponse p rect d lam) := by
  intro v w hvw
  let vv := max d.V0 v
  let ww := max d.V0 w
  have hv : d.V0≤ vv := le_max_left _ _
  have hw : d.V0≤ ww := le_max_left _ _
  have hvw' : vv≤ ww := max_le_max le_rfl hvw
  have hbv := d.response_mem lam hlam vv hv
  have hbw := d.response_mem lam hlam ww hw
  have hfv := d.response_first_order lam hlam vv hv
  have hfw := d.response_first_order lam hlam ww hw
  have hsv := h.derivative.served_pos lam hlam (d.response lam vv) ⟨hbv.1.le,hbv.2⟩
  have hsw := h.derivative.served_pos lam hlam (d.response lam ww) ⟨hbw.1.le,hbw.2⟩
  have heqv : marginalCost p lam (d.response lam vv)=vv := by
    unfold marginalCost
    exact (div_eq_iff hsv.ne').2 (by nlinarith [hfv])
  have heqw : marginalCost p lam (d.response lam ww)=ww := by
    unfold marginalCost
    exact (div_eq_iff hsw.ne').2 (by nlinarith [hfw])
  by_contra hnot
  have hlt : d.response lam ww< d.response lam vv := lt_of_not_ge hnot
  have hh := marginalCost_strictMonoOn p rect h lam hlam
    ⟨hbw.1.le,hbw.2⟩ ⟨hbv.1.le,hbv.2⟩ hlt
  rw [heqw,heqv] at hh
  exact (not_lt_of_ge hvw') hh

theorem canonicalTailResponse_measurable (p : Center) (rect : Rectangle p)
    (h : RectangleAnalyticCertificate p rect) (d : BoundaryTaylorData p rect)
    (lam : Fin 2 → ℝ) (hlam : lam∈rect.box) :
    Measurable (canonicalTailResponse p rect d lam) :=
  (canonicalTailResponse_monotone p rect h d lam hlam).measurable

end FCAppendix.Affine.Hybrid.Tail03
