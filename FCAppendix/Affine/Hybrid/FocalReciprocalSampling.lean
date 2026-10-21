import FCAppendix.Affine.Hybrid.ReciprocalSampling

noncomputable section
namespace FCAppendix.Affine.Hybrid
open MeasureTheory ProbabilityTheory Set Filter Topology Classical
open scoped BigOperators

theorem fixed_focal_subset_reciprocal_L1 {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Measure ℝ) [IsProbabilityMeasure G] {L U b : ℝ} (hL : 0 < L)
    (hbox : ∀ᵐx ∂G,x∈Icc L U) (hb : b∈Icc L U) (D : Finset ι) (hD : D.Nonempty) (i : ι) :
    (∫x : ι→ℝ,|(∑j∈D,(Function.update x i b j)⁻¹)/(D.card:ℝ)-∫y,y⁻¹ ∂G|
      ∂Measure.pi (fun _ : ι=>G)) ≤ (1/L)/Real.sqrt D.card+(1/L)/(D.card:ℝ) := by
  let P:=Measure.pi (fun _ : ι=>G)
  let H:=∫y,y⁻¹ ∂G
  let S : (ι→ℝ)→ℝ:=fun x=>∑j∈D,(x j)⁻¹
  let T : (ι→ℝ)→ℝ:=fun x=>∑j∈D,(Function.update x i b j)⁻¹
  have hc : (0:ℝ)<D.card:=Nat.cast_pos.mpr (Finset.card_pos.mpr hD)
  have hginv : Integrable (fun y : ℝ=>y⁻¹) G:=by
    apply Integrable.of_bound measurable_inv.aestronglyMeasurable (1/L)
    filter_upwards [hbox] with y hy
    rw [Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (hL.trans_le hy.1).le)]
    exact (reciprocal_box_bounds hL hy).2
  have hs (j : ι) : Integrable (fun x : ι→ℝ=>(x j)⁻¹) P:=
    integrable_comp_eval hginv
  have ht (j : ι) : Integrable (fun x : ι→ℝ=>(Function.update x i b j)⁻¹) P:=by
    by_cases hj : j=i
    · subst j
      simpa only [Function.update_self] using (integrable_const (b⁻¹) : Integrable (fun _ : ι→ℝ=>b⁻¹) P)
    · simpa only [Function.update_of_ne hj] using hs j
  have hSi : Integrable S P:=integrable_finsetSum _ (fun j _=>hs j)
  have hTi : Integrable T P:=integrable_finsetSum _ (fun j _=>ht j)
  have hSabs : Integrable (fun x=>|S x/(D.card:ℝ)-H|) P:=((hSi.div_const _).sub (integrable_const H)).abs
  have hTabs : Integrable (fun x=>|T x/(D.card:ℝ)-H|) P:=((hTi.div_const _).sub (integrable_const H)).abs
  have hrows : ∀ᵐx ∂P,∀j,x j∈Icc L U:=ae_all_iff.mpr
    (fun j=>(measurePreserving_eval (fun _ : ι=>G) j).quasiMeasurePreserving.ae hbox)
  have hpoint : ∀ᵐx ∂P,|T x/(D.card:ℝ)-H| ≤ |S x/(D.card:ℝ)-H|+(1/L)/(D.card:ℝ) := by
    filter_upwards [hrows] with x hx
    have hdiff (j : ι) : |(Function.update x i b j)⁻¹-(x j)⁻¹| ≤ if j=i then 1/L else 0 := by
      by_cases hj : j=i
      · subst j
        rw [Function.update_self,if_pos rfl,abs_le]
        have hb0 : 0 ≤ b⁻¹:=inv_nonneg.mpr (hL.trans_le hb.1).le
        have hx0 : 0 ≤ (x i)⁻¹:=inv_nonneg.mpr (hL.trans_le (hx i).1).le
        constructor <;> linarith [(reciprocal_box_bounds hL hb).2,(reciprocal_box_bounds hL (hx i)).2]
      · simp only [Function.update_of_ne hj,sub_self,abs_zero,if_neg hj,le_refl]
    have hsum : |T x-S x| ≤ 1/L:=by
      calc
        _=|∑j∈D,((Function.update x i b j)⁻¹-(x j)⁻¹)|:=by rw [Finset.sum_sub_distrib]
        _ ≤ ∑j∈D,|(Function.update x i b j)⁻¹-(x j)⁻¹|:=Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑j∈D,if j=i then 1/L else 0:=Finset.sum_le_sum (fun j _=>hdiff j)
        _ ≤ 1/L:=by by_cases hi : i∈D <;> simp [hi, hL.le]
    have he : T x/(D.card:ℝ)-H=(S x/(D.card:ℝ)-H)+(T x-S x)/(D.card:ℝ):=by ring
    rw [he]
    apply (abs_add_le _ _).trans
    have hfrac : |(T x-S x)/(D.card:ℝ)| ≤ (1/L)/(D.card:ℝ) := by
      rw [abs_div,abs_of_pos hc]
      exact div_le_div_of_nonneg_right hsum hc.le
    linarith
  have hh:=integral_mono_ae hTabs (hSabs.add (integrable_const _)) hpoint
  simp only [Pi.add_apply] at hh
  rw [integral_add hSabs (integrable_const _),integral_const,probReal_univ,smul_eq_mul,one_mul] at hh
  have hplain:=iid_subset_reciprocal_L1 G hL hbox D hD
  change (∫x, |S x/(D.card:ℝ)-H| ∂P) ≤ _ at hplain
  linarith

end FCAppendix.Affine.Hybrid
