import FCAppendix.Affine.UniformFinite.ActualAtomCrossing
import FCAppendix.Affine.LowBody.FirstCopyNoisyGain

noncomputable section
namespace FCAppendix.Affine.UniformFinite.ActualAtoms
open Set MeasureTheory ProbabilityTheory Filter Topology Classical
open scoped BigOperators

lemma pair_others_above {M : ℕ} (b : Fin M → ℝ) (focal rival : Fin M)
    (_hfr : focal ≠ rival) (u x y : ℝ) (hy : y≤ u) :
    Finset.univ.filter (fun k => k≠focal ∧ u< LowBody.pairBids b focal rival x y k) =
      LowBody.pairRestAbove u focal rival b := by
  ext k
  by_cases hki : k=focal
  · subst k
    simp [LowBody.pairRestAbove]
  by_cases hkj : k=rival
  · subst k
    simp [LowBody.pairRestAbove, LowBody.pairBids, not_lt_of_ge hy]
  · simp [LowBody.pairRestAbove, LowBody.pairBids,
      hki, hkj]

lemma update_pairBids_focal {M : ℕ} (b : Fin M → ℝ) (focal rival : Fin M)
    (hfr : focal ≠ rival) (x y z : ℝ) :
    Function.update (LowBody.pairBids b focal rival x y) focal z =
      LowBody.pairBids b focal rival z y := by
  funext k
  by_cases hkf : k=focal
  · subst k
    simp [LowBody.pairBids, Function.update_of_ne hfr]
  · by_cases hkr : k=rival
    · subst k
      simp [LowBody.pairBids, Function.update_of_ne hkf]
    · simp [LowBody.pairBids, Function.update_of_ne hkf, Function.update_of_ne hkr]

def actualPairGain {M : ℕ} [NeZero M] (i : Uniform07.Row)
    (G : Uniform05.RestrictedLaw i) (row : Source.CountRow M)
    (b : Fin M → ℝ) (focal rival : Fin M) (w x y z : ℝ) : ℝ :=
  rowPayoff i G row w (LowBody.pairBids b focal rival z y) focal -
    rowPayoff i G row w (LowBody.pairBids b focal rival x y) focal

theorem actualPairGain_lower {M : ℕ} [NeZero M] (i : Uniform07.Row)
    (G : Uniform05.RestrictedLaw i) (row : Source.CountRow M)
    (b : Fin M → ℝ) (focal rival : Fin M) (hfr : focal≠rival)
    (hf : focal∈row.lower) (hr : rival∈row.lower)
    (hzero : Source.residual row 1=0)
    (l u w x y z S : ℝ) (hy : y≤ u) (hl : l≤ x) (hz : u< z) (hz0 : 0< z)
    (hS : S≤ w-x)
    (hcount : (LowBody.pairRestAbove u focal rival (Source.lowerBids row b)).card+1 =
      Source.residual row 0) :
    (if focal∉((Source.lowerTemplate row).selection (Uniform05.kappa i)
      (Source.lowerBids row (LowBody.pairBids b focal rival x y))).1 then S else 0)-(z-l) ≤
        actualPairGain i G row b focal rival w x y z := by
  have hlpos : 0< Source.residual row 0 := by omega
  have hh := row_firstCopy_crossing_gain i G row w
    (LowBody.pairBids b focal rival x y) focal hf hlpos hzero l u z S
    (by simpa [LowBody.pairBids, Function.update_of_ne hfr] using hl) hz hz0
    (by simpa [LowBody.pairBids, Function.update_of_ne hfr] using hS) (by
      rw [lowerBids_pairBids row b focal rival hf hr,
        pair_others_above _ focal rival hfr u x y hy]
      omega)
  simpa only [actualPairGain, update_pairBids_focal b focal rival hfr x y z] using hh

lemma measurable_selected_purePayoff {A ι : Type*} [MeasurableSpace A]
    [Fintype ι] [DecidableEq ι] (T : LowBody.PureTemplate ι) (κ : ℝ) (focal : ι)
    (w : A→ℝ) (b : A→ι→ℝ) (hw : Measurable w) (hb : Measurable b) :
    Measurable (fun p => LowBody.purePayoff κ (w p) (b p) (T.selection κ (b p)) focal) := by
  have hc := (measurable_of_countable (fun P : Finset ι×Finset ι =>
    LowBody.focalCopy P focal)).comp ((T.measurable_selection κ).comp hb)
  have hbid := (measurable_pi_apply focal).comp hb
  unfold LowBody.purePayoff
  exact Measurable.ite (measurableSet_eq_fun hc measurable_const)
    (hw.sub (measurable_const.mul hbid))
    (Measurable.ite (measurableSet_eq_fun hc measurable_const)
      (hw.sub hbid) measurable_const)

lemma measurable_pairBids_comp {A : Type*} [MeasurableSpace A] {M : ℕ}
    (b : Fin M→ℝ) (focal rival : Fin M) (x y : A→ℝ)
    (hx : Measurable x) (hy : Measurable y) :
    Measurable (fun p => LowBody.pairBids b focal rival (x p) (y p)) :=
  (LowBody.continuous_pairBids b focal rival).measurable.comp (hx.prodMk hy)

lemma measurable_actualPairGain {A : Type*} [MeasurableSpace A] {M : ℕ} [NeZero M]
    (i : Uniform07.Row) (G : Uniform05.RestrictedLaw i) (row : Source.CountRow M)
    (b : Fin M→ℝ) (focal rival : Fin M) (hf : focal∈row.lower) (hr : rival∈row.lower)
    (hleft : 0< Source.residual row 0) (hzero : Source.residual row 1=0)
    (w x y z : A→ℝ) (hw : Measurable w) (hx : Measurable x)
    (hy : Measurable y) (hz : Measurable z) :
    Measurable (fun p => actualPairGain i G row b focal rival (w p) (x p) (y p) (z p)) := by
  have he (p : A) : actualPairGain i G row b focal rival (w p) (x p) (y p) (z p) =
      LowBody.purePayoff (Uniform05.kappa i) (w p)
        (LowBody.pairBids (Source.lowerBids row b) focal rival (z p) (y p))
        ((Source.lowerTemplate row).selection (Uniform05.kappa i)
          (LowBody.pairBids (Source.lowerBids row b) focal rival (z p) (y p))) focal -
      LowBody.purePayoff (Uniform05.kappa i) (w p)
        (LowBody.pairBids (Source.lowerBids row b) focal rival (x p) (y p))
        ((Source.lowerTemplate row).selection (Uniform05.kappa i)
          (LowBody.pairBids (Source.lowerBids row b) focal rival (x p) (y p))) focal := by
    unfold actualPairGain
    rw [rowPayoff_eq_pure_of_right_zero i G row (w p) _ focal hf hleft hzero,
      rowPayoff_eq_pure_of_right_zero i G row (w p) _ focal hf hleft hzero,
      lowerBids_pairBids row b focal rival hf hr,
      lowerBids_pairBids row b focal rival hf hr]
  simp_rw [he]
  exact (measurable_selected_purePayoff (Source.lowerTemplate row) (Uniform05.kappa i)
    focal w _ hw (measurable_pairBids_comp _ focal rival z y hz hy)).sub
      (measurable_selected_purePayoff (Source.lowerTemplate row) (Uniform05.kappa i)
        focal w _ hw (measurable_pairBids_comp _ focal rival x y hx hy))

section Carrier
variable {A : Type*} [MeasurableSpace A] {M : ℕ} [NeZero M]

theorem normalized_actualPairGain_lower (i : Uniform07.Row)
    (G : Uniform05.RestrictedLaw i) (row : Source.CountRow M)
    (b : Fin M→ℝ) (focal rival : Fin M) (hfr : focal≠rival)
    (hf : focal∈row.lower) (hr : rival∈row.lower)
    (hzero : Source.residual row 1=0) (l u S err W B : ℝ) (hS : 0≤ S)
    (hcount : (LowBody.pairRestAbove u focal rival (Source.lowerBids row b)).card+1 =
      Source.residual row 0)
    (Γ : Measure A) [IsProbabilityMeasure Γ]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] [NullSingletonClass μ]
    (w x z : A→ℝ) (hw : Measurable w) (hx : Measurable x) (hz : Measurable z)
    (hpush : Γ.map x=μ) (hμ : ∀ᵐy∂μ,y≤ u)
    (hbox : ∀ᵐp∂Γ,l≤ x p ∧ x p≤ u ∧ u< z p ∧ 0< z p ∧ S≤ w p-x p ∧
      z p-l≤ err ∧ |w p|≤ W ∧ |x p|≤ B ∧ |z p|≤ B) :
    S/2-err ≤ ∫p : A×ℝ,
      actualPairGain i G row b focal rival (w p.1) (x p.1) p.2 (z p.1) ∂Γ.prod μ := by
  have hlpos : 0< Source.residual row 0 := by omega
  let F : A×ℝ→ℝ := fun p =>
    actualPairGain i G row b focal rival (w p.1) (x p.1) p.2 (z p.1)
  have hFm : Measurable F := measurable_actualPairGain i G row b focal rival hf hr hlpos hzero
    (w ∘ Prod.fst) (x ∘ Prod.fst) Prod.snd (z ∘ Prod.fst)
    (hw.comp measurable_fst) (hx.comp measurable_fst) measurable_snd (hz.comp measurable_fst)
  have hboxP := (Measure.quasiMeasurePreserving_fst (μ:=Γ) (ν:=μ)).ae hbox
  have hFbound : ∀ᵐp∂Γ.prod μ, |F p|≤2*W+2*(1+|Uniform05.eta i|)*B := by
    filter_upwards [hboxP] with p hp
    have hn := rowPayoff_bound i G row (w p.1) (LowBody.pairBids b focal rival (z p.1) p.2) focal
    have ho := rowPayoff_bound i G row (w p.1) (LowBody.pairBids b focal rival (x p.1) p.2) focal
    simp only [LowBody.pairBids, Function.update_of_ne hfr, Function.update_self] at hn ho
    have habs := abs_sub
      (rowPayoff i G row (w p.1) (LowBody.pairBids b focal rival (z p.1) p.2) focal)
      (rowPayoff i G row (w p.1) (LowBody.pairBids b focal rival (x p.1) p.2) focal)
    have hc : 0≤1+|Uniform05.eta i| := by positivity
    have hxB := mul_le_mul_of_nonneg_left hp.2.2.2.2.2.2.2.1 hc
    have hzB := mul_le_mul_of_nonneg_left hp.2.2.2.2.2.2.2.2 hc
    change |F p|≤ _ at habs
    dsimp only [LowBody.pairBids] at habs
    linarith [hp.2.2.2.2.2.2.1]
  have hFi : Integrable F (Γ.prod μ) := Integrable.of_bound hFm.aestronglyMeasurable
    (2*W+2*(1+|Uniform05.eta i|)*B) (by simpa only [Real.norm_eq_abs] using hFbound)
  let R : Set (ℝ×ℝ) := {p | focal∉((Source.lowerTemplate row).selection (Uniform05.kappa i)
    (LowBody.pairBids (Source.lowerBids row b) focal rival p.1 p.2)).1}
  have hR : MeasurableSet R :=
    (((measurable_of_countable (fun P : Allocation M => focal∉P.1)).comp
      (((Source.lowerTemplate row).measurable_selection (Uniform05.kappa i)).comp
        (LowBody.continuous_pairBids (Source.lowerBids row b) focal rival).measurable))).setOf
  let R' : Set (A×ℝ) := (Prod.map x id) ⁻¹' R
  have hR' : MeasurableSet R' := hR.preimage (hx.prodMap measurable_id)
  have hmap : (Γ.prod μ).map (Prod.map x id)=μ.prod μ := by
    rw [← Measure.map_prod_map Γ μ hx measurable_id, hpush, Measure.map_id]
  have hmass : (Γ.prod μ).real R'=(μ.prod μ).real R := by
    rw [← hmap]
    change ((Γ.prod μ) R').toReal=((Γ.prod μ).map (Prod.map x id) R).toReal
    rw [Measure.map_apply (hx.prodMap measurable_id) hR]
  have hreject : 1/2≤(Γ.prod μ).real R' := by
    rw [hmass]
    exact LowBody.pair_rejection_probability_ge_half (Source.lowerTemplate row)
      (Uniform05.kappa i) (Source.lowerBids row b) focal rival hfr hf hr hzero
      (fun k hk => Source.lowerBids_of_not_mem row b hk) u
      (by dsimp only [Source.lowerTemplate]; omega) μ hμ
  have hri : Integrable (R'.indicator (fun _=> S)) (Γ.prod μ) :=
    (integrable_const S).indicator hR'
  have hh := integral_mono_ae (hri.sub (integrable_const err)) hFi (by
    have hy := (Measure.quasiMeasurePreserving_snd (μ:=Γ) (ν:=μ)).ae hμ
    filter_upwards [hboxP, hy] with p hp hyp
    have hpoint := actualPairGain_lower i G row b focal rival hfr hf hr hzero
      l u (w p.1) (x p.1) p.2 (z p.1) S hyp hp.1 hp.2.2.1 hp.2.2.2.1
        hp.2.2.2.2.1 hcount
    rw [lowerBids_pairBids row b focal rival hf hr] at hpoint
    have he : (R'.indicator (fun _=> S)) p =
        if focal∉((Source.lowerTemplate row).selection (Uniform05.kappa i)
          (LowBody.pairBids (Source.lowerBids row b) focal rival (x p.1) p.2)).1
        then S else 0 := by
      simp only [R', R, Set.indicator, Set.mem_preimage, Set.mem_setOf_eq]
      rfl
    change (R'.indicator (fun _=> S)) p-err≤ F p
    rw [he]
    change _≤ F p at hpoint
    linarith [hp.2.2.2.2.2.1])
  simp only [Pi.sub_apply] at hh
  rw [integral_sub hri (integrable_const err), integral_indicator_const _ hR'] at hh
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hh
  nlinarith [mul_le_mul_of_nonneg_left hreject hS]

theorem finite_actualPairGain_lower (i : Uniform07.Row)
    (G : Uniform05.RestrictedLaw i) (row : Source.CountRow M)
    (b : Fin M→ℝ) (focal rival : Fin M) (hfr : focal≠rival)
    (hf : focal∈row.lower) (hr : rival∈row.lower)
    (hzero : Source.residual row 1=0) (l u S err W B : ℝ) (hS : 0≤ S)
    (hcount : (LowBody.pairRestAbove u focal rival (Source.lowerBids row b)).card+1 =
      Source.residual row 0)
    (Γ : Measure A) [IsFiniteMeasure Γ] (hΓ : Γ univ≠0)
    (θ : Measure ℝ) [IsFiniteMeasure θ] [NullSingletonClass θ]
    (w x z : A→ℝ) (hw : Measurable w) (hx : Measurable x) (hz : Measurable z)
    (hpush : Γ.map x=θ) (hθ : ∀ᵐy∂θ,y≤ u)
    (hbox : ∀ᵐp∂Γ,l≤ x p ∧ x p≤ u ∧ u< z p ∧ 0< z p ∧ S≤ w p-x p ∧
      z p-l≤ err ∧ |w p|≤ W ∧ |x p|≤ B ∧ |z p|≤ B) :
    (Γ.real univ)^2*(S/2-err) ≤ ∫p : A×ℝ,
      actualPairGain i G row b focal rival (w p.1) (x p.1) p.2 (z p.1) ∂Γ.prod θ := by
  have hm : θ univ=Γ univ := by
    rw [← hpush, Measure.map_apply hx MeasurableSet.univ, preimage_univ]
  let P : Measure A := (Γ univ)⁻¹ • Γ
  let μ : Measure ℝ := (Γ univ)⁻¹ • θ
  have ht : Γ univ≠⊤ := measure_ne_top Γ univ
  haveI : IsProbabilityMeasure P := ⟨by
    change (Γ univ)⁻¹*Γ univ=1
    exact ENNReal.inv_mul_cancel hΓ ht⟩
  haveI : IsProbabilityMeasure μ := ⟨by
    change (Γ univ)⁻¹*θ univ=1
    rw [hm]
    exact ENNReal.inv_mul_cancel hΓ ht⟩
  haveI : NullSingletonClass μ := ⟨by
    intro x
    simp only [μ, Measure.smul_apply, measure_singleton, smul_eq_mul, mul_zero]⟩
  have hp : P.map x=μ := by simp only [P, μ, Measure.map_smul, hpush]
  have hn := normalized_actualPairGain_lower i G row b focal rival hfr hf hr hzero
    l u S err W B hS hcount P μ w x z hw hx hz hp
    (Measure.ae_smul_measure hθ _) (Measure.ae_smul_measure hbox _)
  have hΓrec : Γ=(Γ univ) • P := by
    dsimp [P]
    rw [smul_smul, ENNReal.mul_inv_cancel hΓ ht, one_smul]
  have hθrec : θ=(Γ univ) • μ := by
    dsimp [μ]
    rw [smul_smul, ENNReal.mul_inv_cancel hΓ ht, one_smul]
  have hprod : Γ.prod θ=(Γ univ*Γ univ) • (P.prod μ) := by
    calc
      Γ.prod θ=((Γ univ) • P).prod ((Γ univ) • μ) := congrArg₂ Measure.prod hΓrec hθrec
      _=(Γ univ*Γ univ) • (P.prod μ) := by
        rw [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul]
  rw [hprod, integral_smul_measure]
  simp only [ENNReal.toReal_pow, smul_eq_mul, measureReal_def, ← pow_two]
  exact mul_le_mul_of_nonneg_left hn (sq_nonneg _)

end Carrier
end FCAppendix.Affine.UniformFinite.ActualAtoms
