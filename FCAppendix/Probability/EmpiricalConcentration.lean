import FCAppendix.Probability.ActiveCountBounds

namespace FCAppendix.Probability
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped BigOperators ProbabilityTheory
variable {α : Type*} [MeasurableSpace α]

theorem iid_empiricalMean_hasSubgaussianMGF
    (μ : Measure α) [IsProbabilityMeasure μ] {f : α → ℝ}
    (hf : AEMeasurable f μ) (hb : ∀ᵐ x ∂μ, f x ∈ Icc (0:ℝ) 1)
    (N : ℕ) (hN : 0 < N) :
    HasSubgaussianMGF
      (fun r : Fin N → α => (∑ i, f (r i))/(N:ℝ)-∫ x, f x ∂μ)
      (1/(4*N):NNReal) (Measure.pi (fun _ : Fin N => μ)) := by
  let P := Measure.pi (fun _ : Fin N => μ)
  let X : Fin N → (Fin N → α) → ℝ := fun i r => f (r i)-∫ x, f x ∂μ
  have hind : iIndepFun X P :=
    iIndepFun_pi (fun _ : Fin N => hf.sub_const _)
  have hsub i : HasSubgaussianMGF (X i) (1/4:NNReal) P := by
    have hp := measurePreserving_eval (fun _ : Fin N => μ) i
    have hm : AEMeasurable (fun r : Fin N → α => f (r i)) P :=
      (hf.aestronglyMeasurable.comp_measurePreserving hp).aemeasurable
    have hh := hasSubgaussianMGF_of_mem_Icc hm (hp.quasiMeasurePreserving.ae hb)
    have he : (∫ r : Fin N → α, f (r i) ∂P) = ∫ x, f x ∂μ :=
      integral_comp_eval hf.aestronglyMeasurable
    rw [he] at hh
    convert hh using 1
    norm_num
  have hs := HasSubgaussianMGF.sum_of_iIndepFun hind (s := Finset.univ) (fun i _ => hsub i)
  have hs' : HasSubgaussianMGF (fun r => ∑ i, X i r) ((N:NNReal)/4) P := by
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one_div] using hs
  convert hs'.const_mul ((N:ℝ)⁻¹) using 1
  · funext r
    simp only [X,Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    field_simp [Nat.cast_ne_zero.mpr hN.ne']
  · apply Subtype.ext
    change (1:ℝ)/(4*(N:ℝ)) = ((N:ℝ)⁻¹)^2*((N:ℝ)/4)
    field_simp [Nat.cast_ne_zero.mpr hN.ne']

theorem iid_empiricalMean_upper_tail_le
    (μ : Measure α) [IsProbabilityMeasure μ] {f : α → ℝ}
    (hf : AEMeasurable f μ) (hb : ∀ᵐ x ∂μ, f x ∈ Icc (0:ℝ) 1)
    (N : ℕ) (hN : 0 < N) {ε : ℝ} (hε : 0 ≤ ε) :
    (Measure.pi (fun _ : Fin N => μ)).real
      {r | ε ≤ (∑ i, f (r i))/(N:ℝ)-∫ x, f x ∂μ} ≤ Real.exp (-2*(N:ℝ)*ε^2) := by
  have hh := (iid_empiricalMean_hasSubgaussianMGF μ hf hb N hN).measure_ge_le hε
  simp only [NNReal.coe_div,NNReal.coe_one,NNReal.coe_mul,NNReal.coe_natCast,NNReal.coe_ofNat] at hh
  have he : -ε^2/(2*(1/(4*(N:ℝ)))) = -2*(N:ℝ)*ε^2 := by
    field_simp [Nat.cast_ne_zero.mpr hN.ne']
    ring
  rwa [he] at hh

theorem iid_empiricalMean_lower_tail_le
    (μ : Measure α) [IsProbabilityMeasure μ] {f : α → ℝ}
    (hf : AEMeasurable f μ) (hb : ∀ᵐ x ∂μ, f x ∈ Icc (0:ℝ) 1)
    (N : ℕ) (hN : 0 < N) {ε : ℝ} (hε : 0 ≤ ε) :
    (Measure.pi (fun _ : Fin N => μ)).real
      {r | ε ≤ (∫ x, f x ∂μ)-(∑ i, f (r i))/(N:ℝ)} ≤ Real.exp (-2*(N:ℝ)*ε^2) := by
  have hh := (iid_empiricalMean_hasSubgaussianMGF μ hf hb N hN).neg.measure_ge_le hε
  simp only [Pi.neg_apply,neg_sub,NNReal.coe_div,NNReal.coe_one,NNReal.coe_mul,
    NNReal.coe_natCast,NNReal.coe_ofNat] at hh
  have he : -ε^2/(2*(1/(4*(N:ℝ)))) = -2*(N:ℝ)*ε^2 := by
    field_simp [Nat.cast_ne_zero.mpr hN.ne']
    ring
  rwa [he] at hh

theorem iid_empiricalMean_two_sided_le
    (μ : Measure α) [IsProbabilityMeasure μ] {f : α → ℝ}
    (hf : AEMeasurable f μ) (hb : ∀ᵐ x ∂μ, f x ∈ Icc (0:ℝ) 1)
    (N : ℕ) (hN : 0 < N) {ε : ℝ} (hε : 0 ≤ ε) :
    (Measure.pi (fun _ : Fin N => μ)).real
      {r | ε ≤ |(∑ i, f (r i))/(N:ℝ)-∫ x, f x ∂μ|} ≤ 2*Real.exp (-2*(N:ℝ)*ε^2) := by
  let E := {r : Fin N → α | ε ≤ (∑ i, f (r i))/(N:ℝ)-∫ x, f x ∂μ}
  let D := {r : Fin N → α | ε ≤ (∫ x, f x ∂μ)-(∑ i, f (r i))/(N:ℝ)}
  have he : {r : Fin N → α | ε ≤ |(∑ i, f (r i))/(N:ℝ)-∫ x, f x ∂μ|} = E ∪ D := by
    ext r
    change (ε ≤ |(∑ i, f (r i))/(N:ℝ)-∫ x, f x ∂μ|) ↔
      (ε ≤ (∑ i, f (r i))/(N:ℝ)-∫ x, f x ∂μ) ∨
      (ε ≤ (∫ x, f x ∂μ)-(∑ i, f (r i))/(N:ℝ))
    constructor
    · intro hr
      by_cases hp : 0 ≤ (∑ i, f (r i))/(N:ℝ)-∫ x, f x ∂μ
      · exact Or.inl (by simpa only [abs_of_nonneg hp] using hr)
      · exact Or.inr (by simpa only [abs_of_nonpos (le_of_not_ge hp),neg_sub] using hr)
    · rintro (hr | hr)
      · exact hr.trans (le_abs_self _)
      · have hh := neg_le_abs ((∑ i, f (r i))/(N:ℝ)-∫ x, f x ∂μ)
        rw [neg_sub] at hh
        exact hr.trans hh
  rw [he]
  have hu := iid_empiricalMean_upper_tail_le μ hf hb N hN hε
  have hl := iid_empiricalMean_lower_tail_le μ hf hb N hN hε
  have hh := (measureReal_union_le (μ := Measure.pi (fun _ : Fin N => μ)) E D).trans (add_le_add hu hl)
  simpa only [two_mul] using hh

theorem iid_event_fraction_two_sided_le
    (μ : Measure α) [IsProbabilityMeasure μ] (E : Set α) (hE : MeasurableSet E)
    (N : ℕ) (hN : 0 < N) {ε : ℝ} (hε : 0 ≤ ε) :
    (Measure.pi (fun _ : Fin N => μ)).real
      {r | ε ≤ |(sampleCount E r:ℝ)/(N:ℝ)-μ.real E|} ≤
        2*Real.exp (-2*(N:ℝ)*ε^2) := by
  classical
  let f := E.indicator (fun _ : α => (1:ℝ))
  have hf : Measurable f := measurable_const.indicator hE
  have hb : ∀ᵐ x ∂μ, f x ∈ Icc (0:ℝ) 1 := Eventually.of_forall fun x => by
    dsimp only [f,indicator]
    split_ifs <;> norm_num
  have hm : (∫ x, f x ∂μ) = μ.real E := integral_indicator_one hE
  have hs (r : Fin N → α) : (∑ i, f (r i)) = (sampleCount E r:ℝ) := by
    simp [f,indicator_apply,sampleCount]
  simpa only [hm,hs] using iid_empiricalMean_two_sided_le μ hf.aemeasurable hb N hN hε

end FCAppendix.Probability
