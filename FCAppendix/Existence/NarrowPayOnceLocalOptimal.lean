import FCAppendix.Existence.NarrowPayOnceStationaryEstimates

noncomputable section
namespace FCAppendix.Existence.NarrowPayOnce
open Set Filter Topology MeasureTheory

namespace FiniteScoreControl
variable {n R c : ℕ} {w0 kappa eps delta : ℝ}
  (U : FiniteScoreControl n R c w0 kappa eps delta)
  (nu : Measure U.valueBand) [IsProbabilityMeasure nu]

theorem expected_utility_continuous_positive (beta : U.valueBand→ℝ) (hbeta : Continuous beta)
    (hb : ∀v,beta v∈Icc (U.B-eps) (U.B+eps)) (w : ℝ) :
    Continuous (fun z : Ioi (0:ℝ)=>finiteExpectedUtility (R:=R) n c nu beta w z.1) := by
  let P : ProbabilityMeasure (Fin R→U.valueBand):=⟨Measure.pi (fun _=>nu),inferInstance⟩
  let f : Ioi (0:ℝ)×(Fin R→U.valueBand)→ℝ:=fun t=>finiteRowUtility n c beta w t.1.1 t.2
  have hf : Continuous f := by
    rw [continuous_iff_continuousAt]
    intro t
    have hh := continuousAt_finiteRowUtility_joint (c:=c) U.n_ge beta hbeta
      (fun v=>U.lower_pos.trans_le (hb v).1) w (t.1.1,t.2) t.1.2
    exact hh.comp (f:=fun x : Ioi (0:ℝ)×(Fin R→U.valueBand)=>(x.1.1,x.2)) (x:=t)
      (continuous_fst.subtype_val.prodMk continuous_snd).continuousAt
  exact (Distributional.continuous_law_integral f hf).comp
    (continuous_id.prodMk (continuous_const (y:=P)))

theorem stationary_local_optimal (beta : U.strategyBand)
    (hroot : ∀v : U.valueBand,finiteExpectedScore (R:=R) n c nu beta.val v (beta.val v)=0)
    (v : U.valueBand) (z : ℝ) (hz : z∈Icc (U.B-eps) (U.B+eps)) :
    finiteExpectedUtility (R:=R) n c nu beta.val v z≤
      finiteExpectedUtility (R:=R) n c nu beta.val v (beta.val v) := by
  let b := beta.val v
  let f := finiteExpectedUtility (R:=R) n c nu beta.val v
  have hb := beta.property v
  have hbi : b∈Ioo (U.B-eps) (U.B+eps) := by
    let D := U.finiteScoreData nu
    have he : D.reply beta v=b := (D.root_unique beta v hb (hroot v)).symm
    rw [← he]
    exact D.reply_mem beta v
  have hc : ContinuousOn f (Icc (U.B-eps) (U.B+eps)) := by
    have hh : ContinuousOn f (Ioi (0:ℝ)) := by
      rw [continuousOn_iff_continuous_restrict]
      exact U.expected_utility_continuous_positive nu beta.val beta.val.continuous beta.property v
    exact hh.mono (fun x hx=>U.lower_pos.trans_le hx.1)
  have hd (x : ℝ) (hx : x∈Ioo (U.B-eps) (U.B+eps)) :
      HasDerivAt f (finiteExpectedScore (R:=R) n c nu beta.val v x) x := by
    apply hasDerivAt_finiteExpectedUtility U.n_ge (by have:=U.c_le; omega) nu beta.val
      beta.val.continuous (fun v=>U.lower_pos.trans_le (beta.property v).1) v
      (U.B-eps) (U.B+eps) x U.lower_pos hx
    intro x hx omega
    exact U.interior _ (U.row_box beta.val beta.property x ⟨hx.1.le,hx.2.le⟩ omega)
  rcases le_total z b with hzb | hbz
  · have hsub : Icc z b⊆Icc (U.B-eps) (U.B+eps) := Icc_subset_Icc hz.1 hb.2
    have hxoo (x : ℝ) (hx : x∈_root_.interior (Icc z b)) : x∈Ioo (U.B-eps) (U.B+eps) := by
      rw [interior_Icc] at hx
      exact ⟨hz.1.trans_lt hx.1,hx.2.trans hbi.2⟩
    have hmono := monotoneOn_of_deriv_nonneg (convex_Icc z b) (hc.mono hsub)
      (fun x hx=>(hd x (hxoo x hx)).differentiableAt.differentiableWithinAt)
      (fun x hx=>by
        rw [(hd x (hxoo x hx)).deriv]
        have hx' := interior_subset hx
        have hh := U.expected_decrease nu beta.val beta.val.continuous beta.property v x b
          (hsub hx') hb hx'.2
        rw [hroot v] at hh
        have hm := mul_nonneg U.own_pos.le (sub_nonneg.mpr hx'.2)
        linarith)
    exact hmono ⟨le_rfl,hzb⟩ ⟨hzb,le_rfl⟩ hzb
  · have hsub : Icc b z⊆Icc (U.B-eps) (U.B+eps) := Icc_subset_Icc hb.1 hz.2
    have hxoo (x : ℝ) (hx : x∈_root_.interior (Icc b z)) : x∈Ioo (U.B-eps) (U.B+eps) := by
      rw [interior_Icc] at hx
      exact ⟨hbi.1.trans hx.1,hx.2.trans_le hz.2⟩
    have hanti := antitoneOn_of_deriv_nonpos (convex_Icc b z) (hc.mono hsub)
      (fun x hx=>(hd x (hxoo x hx)).differentiableAt.differentiableWithinAt)
      (fun x hx=>by
        rw [(hd x (hxoo x hx)).deriv]
        have hx' := interior_subset hx
        have hh := U.expected_decrease nu beta.val beta.val.continuous beta.property v b x
          hb (hsub hx') hx'.1
        rw [hroot v] at hh
        have hm := mul_nonneg U.own_pos.le (sub_nonneg.mpr hx'.1)
        linarith)
    exact hanti ⟨le_rfl,hbz⟩ ⟨hbz,le_rfl⟩ hbz

end FiniteScoreControl
end FCAppendix.Existence.NarrowPayOnce
