import FCAppendix.Affine.LowBody.FirstCopyPair

noncomputable section
namespace FCAppendix.Affine.LowBody
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators
variable {ι X : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace X]

omit [Fintype ι] in
lemma measurable_pairBids_joint (b : X→ι→ℝ) (hb : Measurable b) (i j : ι) :
    Measurable (fun z : X×(ℝ×ℝ)=>pairBids (b z.1) i j z.2.1 z.2.2) := by
  apply measurable_pi_lambda
  intro k
  by_cases hkj : k=j
  · subst k
    simp only [pairBids,Function.update_self]
    exact measurable_snd.snd
  · by_cases hki : k=i
    · subst k
      simp only [pairBids,Function.update_of_ne hkj,Function.update_self]
      exact measurable_snd.fst
    · simp only [pairBids,Function.update_of_ne hkj,Function.update_of_ne hki]
      exact ((measurable_pi_apply k).comp hb).comp measurable_fst

theorem integrated_pair_rejection_ge_half (T : PureTemplate ι) (κ : ℝ)
    (b : X→ι→ℝ) (hb : Measurable b) (i j : ι) (hij : i≠j)
    (hi : i∈T.support) (hj : j∈T.support) (hzero : T.residual₁=0)
    (hz : ∀z k,k∉T.support → b z k=0)
    (u : ℝ) (E : Set X) (hE : MeasurableSet E)
    (hcount : ∀z∈E,T.residual₀-1≤(pairRestAbove u i j (b z)).card)
    (ν : Measure X) [IsProbabilityMeasure ν] (μ : Measure ℝ) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] (hμ : ∀ᵐx ∂μ,x≤u) :
    ν.real E/2 ≤ ∫z in E,
      (μ.prod μ).real {p : ℝ×ℝ | i∉(T.selection κ (pairBids (b z) i j p.1 p.2)).1} ∂ν := by
  classical
  let f : X×(ℝ×ℝ)→ℝ:=fun z=>
    if i∉(T.selection κ (pairBids (b z.1) i j z.2.1 z.2.2)).1 then 1 else 0
  have hm : Measurable f := Measurable.ite
    (((measurable_of_countable (fun P : Finset ι × Finset ι=>i∉P.1)).comp
      ((T.measurable_selection κ).comp (measurable_pairBids_joint b hb i j))).setOf)
    measurable_const measurable_const
  have hf : Integrable f (ν.prod (μ.prod μ)) := Integrable.of_bound hm.aestronglyMeasurable 1
    (Eventually.of_forall (fun z=>by dsimp [f];split_ifs <;> norm_num))
  have hinner (z : X) : (∫p : ℝ×ℝ,f (z,p) ∂μ.prod μ)=
      (μ.prod μ).real {p : ℝ×ℝ | i∉(T.selection κ (pairBids (b z) i j p.1 p.2)).1} := by
    have hme : MeasurableSet {p : ℝ×ℝ | i∉(T.selection κ (pairBids (b z) i j p.1 p.2)).1} :=
      (((measurable_of_countable (fun P : Finset ι × Finset ι=>i∉P.1)).comp
        ((T.measurable_selection κ).comp (continuous_pairBids (b z) i j).measurable))).setOf
    simpa only [f,Set.indicator,Set.mem_setOf_eq,Pi.one_apply] using
      (integral_indicator_one (μ:=μ.prod μ) hme)
  have hfi : Integrable (fun z=>∫p : ℝ×ℝ,f (z,p) ∂μ.prod μ) ν := hf.integral_prod_left
  have hh := integral_mono_ae
    ((integrable_const (1/2:ℝ)).indicator hE) (hfi.indicator hE)
    (Eventually.of_forall (fun z=>by
      by_cases hzE : z∈E
      · simp only [Set.indicator_of_mem hzE]
        rw [hinner]
        exact pair_rejection_probability_ge_half T κ (b z) i j hij hi hj hzero (hz z) u
          (hcount z hzE) μ hμ
      · simp only [Set.indicator_of_notMem hzE,le_refl]))
  rw [integral_indicator_const _ hE,integral_indicator hE] at hh
  simp only [smul_eq_mul,div_eq_mul_inv] at hh
  simpa only [hinner,div_eq_mul_inv,one_mul] using hh

theorem integrated_variable_pair_rejection_ge_half
    {K : Type*} [Countable K] [MeasurableSpace K] [MeasurableSingletonClass K]
    (T : K→PureTemplate ι) (kind : X→K) (hk : Measurable kind) (κ : ℝ)
    (b : X→ι→ℝ) (hb : Measurable b) (i j : ι) (hij : i≠j)
    (hi : ∀z,i∈(T (kind z)).support) (hj : ∀z,j∈(T (kind z)).support)
    (u : ℝ) (E : Set X) (hE : MeasurableSet E)
    (hzero : ∀z∈E,(T (kind z)).residual₁=0)
    (hz : ∀z k,k∉(T (kind z)).support → b z k=0)
    (hcount : ∀z∈E,(T (kind z)).residual₀-1≤(pairRestAbove u i j (b z)).card)
    (ν : Measure X) [IsProbabilityMeasure ν] (μ : Measure ℝ) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] (hμ : ∀ᵐx ∂μ,x≤u) :
    ν.real E/2 ≤ ∫z in E,
      (μ.prod μ).real {p : ℝ×ℝ | i∉((T (kind z)).selection κ (pairBids (b z) i j p.1 p.2)).1} ∂ν := by
  classical
  let f : X×(ℝ×ℝ)→ℝ:=fun z=>
    if i∉((T (kind z.1)).selection κ (pairBids (b z.1) i j z.2.1 z.2.2)).1 then 1 else 0
  have hSel : Measurable (fun q : K×(ι→ℝ)=>(T q.1).selection κ q.2) :=
    measurable_from_prod_countable_right (fun k=>(T k).measurable_selection κ)
  have hm : Measurable f := Measurable.ite
    (((measurable_of_countable (fun P : Finset ι × Finset ι=>i∉P.1)).comp
      (hSel.comp (((hk.comp measurable_fst).prodMk (measurable_pairBids_joint b hb i j))))).setOf)
    measurable_const measurable_const
  have hf : Integrable f (ν.prod (μ.prod μ)) := Integrable.of_bound hm.aestronglyMeasurable 1
    (Eventually.of_forall (fun z=>by dsimp [f];split_ifs <;> norm_num))
  have hinner (z : X) : (∫p : ℝ×ℝ,f (z,p) ∂μ.prod μ)=
      (μ.prod μ).real {p : ℝ×ℝ | i∉((T (kind z)).selection κ (pairBids (b z) i j p.1 p.2)).1} := by
    have hme : MeasurableSet {p : ℝ×ℝ | i∉((T (kind z)).selection κ (pairBids (b z) i j p.1 p.2)).1} :=
      (((measurable_of_countable (fun P : Finset ι × Finset ι=>i∉P.1)).comp
        (((T (kind z)).measurable_selection κ).comp (continuous_pairBids (b z) i j).measurable))).setOf
    simpa only [f,Set.indicator,Set.mem_setOf_eq,Pi.one_apply] using
      (integral_indicator_one (μ:=μ.prod μ) hme)
  have hfi : Integrable (fun z=>∫p : ℝ×ℝ,f (z,p) ∂μ.prod μ) ν := hf.integral_prod_left
  have hh := integral_mono_ae
    ((integrable_const (1/2:ℝ)).indicator hE) (hfi.indicator hE)
    (Eventually.of_forall (fun z=>by
      by_cases hzE : z∈E
      · simp only [Set.indicator_of_mem hzE]
        rw [hinner]
        exact pair_rejection_probability_ge_half (T (kind z)) κ (b z) i j hij (hi z) (hj z)
          (hzero z hzE) (hz z) u (hcount z hzE) μ hμ
      · simp only [Set.indicator_of_notMem hzE,le_refl]))
  rw [integral_indicator_const _ hE,integral_indicator hE] at hh
  simp only [smul_eq_mul,div_eq_mul_inv] at hh
  simpa only [hinner,div_eq_mul_inv,one_mul] using hh

end FCAppendix.Affine.LowBody
