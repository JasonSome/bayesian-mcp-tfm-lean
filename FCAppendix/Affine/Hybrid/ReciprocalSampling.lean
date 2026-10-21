import FCAppendix.Affine.Hybrid.SourceTypicalGuardedData
import FCAppendix.Probability.EmpiricalMean

noncomputable section
namespace FCAppendix.Affine.Hybrid
open MeasureTheory ProbabilityTheory Set Filter Topology Classical
open scoped BigOperators ProbabilityTheory

theorem iid_subsetMean_L1_le {α ι : Type*} [MeasurableSpace α] [Fintype ι] [DecidableEq ι]
    (μ : Measure α) [IsProbabilityMeasure μ] {f : α→ℝ}
    (hf : AEStronglyMeasurable f μ) (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ᵐx ∂μ,|f x| ≤ B) (D : Finset ι) (hD : D.Nonempty) :
    (∫x : ι→α,|(∑i∈D,f (x i))/(D.card:ℝ)-∫y,f y ∂μ|
      ∂Measure.pi (fun _ : ι=>μ)) ≤ B/Real.sqrt D.card := by
  let P:=Measure.pi (fun _ : ι=>μ)
  let S : (ι→α)→ℝ:=fun x=>∑i∈D,f (x i)
  have hcard : 0<D.card:=Finset.card_pos.mpr hD
  have hc : (0:ℝ)<D.card:=Nat.cast_pos.mpr hcard
  have hL : MemLp f 2 μ:=MemLp.of_bound hf B (by simpa only [Real.norm_eq_abs] using hb)
  have hLi (i : ι) : MemLp (fun x : ι→α=>f (x i)) 2 P:=
    hL.comp_measurePreserving (measurePreserving_eval (fun _ : ι=>μ) i)
  have hS : MemLp S 2 P:=memLp_finsetSum _ (fun i _=>hLi i)
  have hmean : MemLp (fun x=>S x/(D.card:ℝ)) 2 P:=by
    simpa only [div_eq_mul_inv] using hS.mul_const ((D.card:ℝ)⁻¹)
  have hi : (∫x,S x/(D.card:ℝ) ∂P)=∫y,f y ∂μ := by
    rw [integral_div]
    have hs : (∫x,S x ∂P)=(D.card:ℝ)*∫y,f y ∂μ := by
      rw [show S=(fun x=>∑i∈D,f (x i)) from rfl,
        integral_finsetSum _ (fun i _=>(hLi i).integrable (by norm_num))]
      have he (i : ι) : (∫x : ι→α,f (x i) ∂P)=∫y,f y ∂μ:=integral_comp_eval hf
      simp only [he,Finset.sum_const,nsmul_eq_mul]
    rw [hs,mul_div_cancel_left₀ _ hc.ne']
  have hvar : variance (fun x=>S x/(D.card:ℝ)) P=variance f μ/D.card := by
    have hs : variance S P=(D.card:ℝ)*variance f μ := by
      have hh:=IndepFun.variance_sum (s:=D) (fun i _=>hLi i)
        (fun i _ j _ hij=>(iIndepFun_pi (fun _ : ι=>hL.aemeasurable)).indepFun hij)
      have hfun : (∑i∈D,fun x : ι→α=>f (x i))=S:=by ext x;simp only [Finset.sum_apply,S]
      rw [hfun] at hh
      have he (i : ι) : variance (fun x : ι→α=>f (x i)) P=variance f μ := by
        change variance (f ∘ fun x : ι→α=>x i) P=variance f μ
        rw [←variance_map,(measurePreserving_eval (fun _ : ι=>μ) i).map_eq]
        · rw [(measurePreserving_eval (fun _ : ι=>μ) i).map_eq]
          exact hL.aemeasurable
        · exact (measurable_pi_apply i).aemeasurable
      simpa only [he,Finset.sum_const,nsmul_eq_mul] using hh
    simp only [div_eq_mul_inv,variance_mul_const,hs]
    field_simp
  have hv : variance f μ ≤ B^2:=by
    apply (variance_le_expectation_sq hL.aestronglyMeasurable).trans
    calc
      (∫x,f x^2 ∂μ) ≤ ∫_x,B^2 ∂μ:=by
        apply integral_mono_ae hL.integrable_sq (integrable_const _)
        filter_upwards [hb] with x hx
        nlinarith [sq_abs (f x),abs_nonneg (f x)]
      _=B^2:=by simp
  have hh:=FCAppendix.Probability.integral_abs_sub_integral_le_sqrt_variance P hmean
  rw [hi,hvar] at hh
  apply hh.trans
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity,?_⟩
  rw [div_pow,Real.sq_sqrt hc.le]
  exact div_le_div_of_nonneg_right hv hc.le

lemma reciprocal_box_bounds {L U b : ℝ} (hL : 0 < L) (hb : b∈Icc L U) :
    1/U ≤ b⁻¹ ∧ b⁻¹ ≤ 1/L := by
  simpa only [one_div] using
    And.intro (one_div_le_one_div_of_le (hL.trans_le hb.1) hb.2)
      (one_div_le_one_div_of_le hL hb.1)

theorem iid_subset_reciprocal_L1 {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Measure ℝ) [IsProbabilityMeasure G] {L U : ℝ} (hL : 0 < L)
    (hbox : ∀ᵐb ∂G,b∈Icc L U) (D : Finset ι) (hD : D.Nonempty) :
    (∫b : ι→ℝ,|(∑i∈D,(b i)⁻¹)/(D.card:ℝ)-∫x,x⁻¹ ∂G|
      ∂Measure.pi (fun _ : ι=>G)) ≤ (1/L)/Real.sqrt D.card := by
  apply iid_subsetMean_L1_le G measurable_inv.aestronglyMeasurable (1/L) (by positivity) _ D hD
  filter_upwards [hbox] with b hb
  rw [abs_of_nonneg (inv_nonneg.mpr (hL.trans_le hb.1).le)]
  exact (reciprocal_box_bounds hL hb).2

end FCAppendix.Affine.Hybrid
