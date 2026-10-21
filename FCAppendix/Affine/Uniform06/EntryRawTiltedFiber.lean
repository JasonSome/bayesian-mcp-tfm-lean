import FCAppendix.Affine.Uniform06.EntrySignFiber
import FCAppendix.Affine.Uniform06.RawMixedSource
import FCAppendix.Probability.TiltedProduct
import FCAppendix.Probability.BoundedTiltVariance

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.EntryRawTiltedFiber

open MeasureTheory ProbabilityTheory Set Filter Topology LowBody
open FCAppendix.Affine.Uniform07 FCAppendix.Affine.ClippedResidual
open FCAppendix.ExponentialTilt
open scoped BigOperators

theorem integral_rivalLaw (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (L : Measure ℝ) [IsProbabilityMeasure L]
    (F : RowRival → ℝ) (hF : Measurable F)
    (hL : Integrable (fun z => F ((0:Fin 4),z)) L) :
    (∫ r, F r ∂rivalLaw t 0 (1-t) L)=
      t*(∫ z, F ((0:Fin 4),z) ∂L)+
        ((1-t)/2)*F (2,0)+((1-t)/2)*F (3,0) := by
  let embed : ℝ → RowRival := fun z => (0,z)
  have he : Measurable embed := measurable_const.prodMk measurable_id
  have hi : Integrable F (L.map embed) :=
    (integrable_map_measure hF.aestronglyMeasurable he.aemeasurable).mpr hL
  have h2 : Integrable F (Measure.dirac ((2:Fin 4),(0:ℝ))) := integrable_dirac (by finiteness)
  have h3 : Integrable F (Measure.dirac ((3:Fin 4),(0:ℝ))) := integrable_dirac (by finiteness)
  unfold rivalLaw
  simp only [ENNReal.ofReal_zero,zero_smul,add_zero]
  rw [integral_add_measure ((hi.smul_measure ENNReal.ofReal_ne_top).add_measure
      (h2.smul_measure ENNReal.ofReal_ne_top)) (h3.smul_measure ENNReal.ofReal_ne_top),
    integral_add_measure (hi.smul_measure ENNReal.ofReal_ne_top) (h2.smul_measure ENNReal.ofReal_ne_top),
    integral_smul_measure,integral_smul_measure,integral_smul_measure,
    integral_dirac,integral_dirac,integral_map he.aemeasurable hF.aestronglyMeasurable,
    ENNReal.toReal_ofReal ht,ENNReal.toReal_ofReal (by linarith : 0 ≤ (1-t)/2)]
  rfl

def lowerTilt (i : Row) (G : Measure (ℝ × ℝ)) (b u : ℝ) : Measure ℝ :=
  (G.map Prod.snd).tilted (fun z => u*exposure (xi i) b z)

def rawTilt (i : Row) (G : Measure (ℝ × ℝ)) (b u : ℝ) : Measure RowRival :=
  (RawMixedSource.source i G).tilted (fun r => u*RawMixedSource.demand (xi i) b r)

def lowerMass (i : Row) (G : Measure (ℝ × ℝ)) (b u : ℝ) : ℝ :=
  cutoff i*Real.exp (cgf (exposure (xi i) b) (G.map Prod.snd) u-
    cgf (RawMixedSource.demand (xi i) b) (RawMixedSource.source i G) u)

def upperMass (i : Row) (G : Measure (ℝ × ℝ)) (b u : ℝ) : ℝ :=
  (1-cutoff i)*Real.exp (u/2-
    cgf (RawMixedSource.demand (xi i) b) (RawMixedSource.source i G) u)

theorem lowerTilt_probability (i : Row) (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    {b : ℝ} (hb : 0 < b) (u : ℝ) : IsProbabilityMeasure (lowerTilt i G b u) := by
  letI : IsProbabilityMeasure (G.map Prod.snd) :=
    Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  exact isProbabilityMeasure_unitInterval_tilted (G.map Prod.snd)
    (continuous_exposure (xi_pos i) hb).measurable
    (ae_of_all _ fun z => ⟨exposure_nonneg (xi_pos i) hb,exposure_le_one _ _ _⟩) u

theorem rawTilt_probability (i : Row) (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    {b : ℝ} (hb : 0 < b) (u : ℝ) : IsProbabilityMeasure (rawTilt i G b u) :=
  isProbabilityMeasure_unitInterval_tilted (RawMixedSource.source i G)
    (RawMixedSource.measurable_demand _ _)
    (ae_of_all _ (RawMixedSource.demand_bounds (xi_pos i) hb)) u

theorem integral_rawTilt (i : Row) (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    {b : ℝ} (hb : 0 < b) (u : ℝ) (F : RowRival → ℝ) (hF : Measurable F)
    {M : ℝ} (_hM : 0 ≤ M) (hbound : ∀ r, |F r| ≤ M) :
    (∫ r, F r ∂rawTilt i G b u)=
      lowerMass i G b u*(∫ z, F ((0:Fin 4),z) ∂lowerTilt i G b u)+
        (upperMass i G b u/2)*F (2,0)+(upperMass i G b u/2)*F (3,0) := by
  let L := G.map Prod.snd
  let ν := RawMixedSource.source i G
  let X := exposure (xi i) b
  let Y := RawMixedSource.demand (xi i) b
  let a := cgf X L u
  let c := cgf Y ν u
  letI : IsProbabilityMeasure L := Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  have hX : Measurable X := (continuous_exposure (xi_pos i) hb).measurable
  have hY : Measurable Y := RawMixedSource.measurable_demand _ _
  have hXunit : ∀ z, X z ∈ Icc (0:ℝ) 1 :=
    fun z => ⟨exposure_nonneg (xi_pos i) hb,exposure_le_one _ _ _⟩
  have hYunit := RawMixedSource.demand_bounds (xi_pos i) hb
  have htL := integrable_exp_mul_of_bounded L hX.aemeasurable (ae_of_all _ hXunit) u
  have htν := integrable_exp_mul_of_bounded ν hY.aemeasurable (ae_of_all _ hYunit) u
  have hemb : Measurable (fun z : ℝ => ((0:Fin 4),z)) := measurable_const.prodMk measurable_id
  let H : RowRival → ℝ := fun r => Real.exp (u*Y r-c)*F r
  have hH : Measurable H := ((hY.const_mul u).sub_const c).exp.mul hF
  have hHlow : Integrable (fun z => H ((0:Fin 4),z)) L := by
    apply Integrable.of_bound (hH.comp hemb).aestronglyMeasurable
      (Real.exp (|u|+|c|)*M)
    apply ae_of_all
    intro z
    have he : Real.exp (u*X z-c) ≤ Real.exp (|u|+|c|) := by
      apply Real.exp_le_exp.mpr
      have hx := hXunit z
      have hm : u*X z ≤ |u| := by
        calc
          u*X z ≤ |u| *X z := mul_le_mul_of_nonneg_right (le_abs_self u) hx.1
          _ ≤ |u| := by nlinarith [abs_nonneg u,hx.2]
      linarith [neg_le_abs c]
    change ‖Real.exp (u*Y ((0:Fin 4),z)-c)*F ((0:Fin 4),z)‖ ≤ _
    have hYX : Y ((0:Fin 4),z)=X z := by simp [Y,X,RawMixedSource.demand]
    rw [hYX,Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul he (hbound _) (abs_nonneg _) (Real.exp_pos _).le
  have hfL : Integrable (fun z => F ((0:Fin 4),z)) (lowerTilt i G b u) := by
    letI := lowerTilt_probability i G hb u
    exact Integrable.of_bound (hF.comp hemb).aestronglyMeasurable M
      (ae_of_all _ fun z => by simpa only [Real.norm_eq_abs] using hbound ((0:Fin 4),z))
  have heLow : (∫ z, H ((0:Fin 4),z) ∂L)=
      Real.exp (a-c)*(∫ z, F ((0:Fin 4),z) ∂lowerTilt i G b u) := by
    rw [lowerTilt,integral_tilted_mul_eq_cgf _ htL]
    simp only [smul_eq_mul]
    rw [← integral_const_mul]
    apply integral_congr_ae
    apply ae_of_all
    intro z
    change Real.exp (u*Y ((0:Fin 4),z)-c)*F ((0:Fin 4),z)=_
    have hYX : Y ((0:Fin 4),z)=X z := by simp [Y,X,RawMixedSource.demand]
    rw [hYX]
    have he : Real.exp (a-c)*Real.exp (u*X z-a)=Real.exp (u*X z-c) := by
      rw [← Real.exp_add]
      congr 1
      ring
    change _=Real.exp (a-c)*(Real.exp (u*X z-a)*F ((0:Fin 4),z))
    rw [← mul_assoc,he]
  have h2 : H (2,0)=Real.exp (u/2-c)*F (2,0) := by
    simp only [H,Y,RawMixedSource.demand,show (2:Fin 4)≠0 by decide,
      show (2:Fin 4)≠1 by decide,if_false]
    ring_nf
  have h3 : H (3,0)=Real.exp (u/2-c)*F (3,0) := by
    simp only [H,Y,RawMixedSource.demand,show (3:Fin 4)≠0 by decide,
      show (3:Fin 4)≠1 by decide,if_false]
    ring_nf
  rw [rawTilt,integral_tilted_mul_eq_cgf _ htν]
  simp only [smul_eq_mul]
  change (∫ r, H r ∂rivalLaw (cutoff i) 0 (1-cutoff i) L)=_
  rw [integral_rivalLaw (cutoff i) (cutoff_pos i).le (cutoff_lt_one i).le L H hH hHlow,
    heLow,h2,h3]
  dsimp only [lowerMass,upperMass,a,c,X,Y,L,ν]
  ring

theorem mass_sum (i : Row) (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    {b : ℝ} (hb : 0 < b) (u : ℝ) :
    lowerMass i G b u+upperMass i G b u=1 := by
  letI := rawTilt_probability i G hb u
  letI := lowerTilt_probability i G hb u
  have hh := integral_rawTilt i G hb u (fun _ => 1) measurable_const
    (by norm_num : (0:ℝ) ≤ 1) (fun _ => by norm_num : ∀ r : RowRival, |(1:ℝ)| ≤ 1)
  simp only [integral_const,probReal_univ,one_smul,mul_one] at hh
  linarith

theorem mass_bounds (i : Row) (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    {b : ℝ} (hb : 0 < b) (u : ℝ) :
    0 < lowerMass i G b u ∧ lowerMass i G b u < 1 ∧
      upperMass i G b u=1-lowerMass i G b u := by
  have hl : 0 < lowerMass i G b u := mul_pos (cutoff_pos i) (Real.exp_pos _)
  have hu : 0 < upperMass i G b u := mul_pos (sub_pos.mpr (cutoff_lt_one i)) (Real.exp_pos _)
  have hs := mass_sum i G hb u
  exact ⟨hl,by linarith,by linarith⟩

theorem rawTilt_eq_rivalLaw (i : Row) (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    {b : ℝ} (hb : 0 < b) (u : ℝ) :
    rawTilt i G b u=rivalLaw (lowerMass i G b u) 0 (1-lowerMass i G b u)
      (lowerTilt i G b u) := by
  have hm := mass_bounds i G hb u
  letI := rawTilt_probability i G hb u
  letI := lowerTilt_probability i G hb u
  letI : IsProbabilityMeasure
      (rivalLaw (lowerMass i G b u) 0 (1-lowerMass i G b u) (lowerTilt i G b u)) :=
    rivalLaw_isProbability _ _ _ hm.1.le le_rfl (sub_nonneg.mpr hm.2.1.le) (by ring) _
  ext S hS
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  let F : RowRival → ℝ := S.indicator (fun _ => 1)
  have hF : Measurable F := measurable_const.indicator hS
  have hFb : ∀ r, |F r| ≤ 1 := by intro r; by_cases hr : r ∈ S <;> simp [F,hr]
  have hFi : Integrable (fun z => F ((0:Fin 4),z)) (lowerTilt i G b u) :=
    Integrable.of_bound (hF.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable 1
      (ae_of_all _ fun z => by simpa only [Real.norm_eq_abs] using hFb ((0:Fin 4),z))
  have he := integral_rawTilt i G hb u F hF (by norm_num : (0:ℝ) ≤ 1) hFb
  rw [hm.2.2] at he
  rw [← integral_rivalLaw (lowerMass i G b u) hm.1.le hm.2.1.le
    (lowerTilt i G b u) F hF hFi] at he
  simpa only [F,integral_indicator_const (1:ℝ) hS,smul_eq_mul,mul_one,measureReal_def] using he

theorem iid_rawTilt_eq_mask_source (i : Row) (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    {b : ℝ} (hb : 0 < b) (u : ℝ) (N : ℕ) :
    (Measure.pi (fun _ : Fin N => RawMixedSource.source i G)).tilted
      (fun r => u*iidSum (RawMixedSource.demand (xi i) b) N r)=
      Measure.pi (fun _ : Fin N => rivalLaw (lowerMass i G b u) 0
        (1-lowerMass i G b u) (lowerTilt i G b u)) := by
  rw [← pi_tilted_eq_tilted_iidSum]
  apply congrArg Measure.pi
  funext j
  exact rawTilt_eq_rivalLaw i G hb u

theorem integral_actual_tilted_mask_sign (i : Row) (G : Measure (ℝ × ℝ))
    [IsProbabilityMeasure G] {b : ℝ} (hb : 0 < b) (u : ℝ) (N : ℕ)
    (F : (Fin N → RowRival) → ℝ) (hF : Measurable F)
    {M : ℝ} (hbound : ∀ r, |F r| ≤ M) :
    (∫ r, F r ∂(Measure.pi (fun _ : Fin N => RawMixedSource.source i G)).tilted
      (fun r => u*iidSum (RawMixedSource.demand (xi i) b) N r))=
      (CommonList.iid (IndependentCounts.bernoulli (lowerMass i G b u)
        (mass_bounds i G hb u).1.le (mass_bounds i G hb u).2.1.le) N).expect (fun low =>
        (CommonList.iid EntrySignFiber.fairSign N).expect (fun sign =>
          ∫ B : Fin N → ℝ, F (fun j => EntrySignFiber.rawRowPoint
            (EntrySignFiber.tag (low j,sign j),B j))
            ∂Measure.pi (fun _ : Fin N => lowerTilt i G b u))) := by
  letI := lowerTilt_probability i G hb u
  rw [iid_rawTilt_eq_mask_source i G hb u]
  exact EntrySignFiber.integral_original_mask_sign _ (mass_bounds i G hb u).1.le
    (mass_bounds i G hb u).2.1.le (lowerTilt i G b u) N F hF M hbound

theorem original_moderate_sign_fiber (i : Row) (G : Measure (ℝ × ℝ))
    [IsProbabilityMeasure G] {b θ : ℝ} (hb : 0 < b) (N : ℕ)
    (F : (Fin N → RowRival) → ℝ) (hF : Measurable F)
    {M : ℝ} (hbound : ∀ r, |F r| ≤ M) :
    let tθ := lowerMass i G b (-θ)
    let Lθ := lowerTilt i G b (-θ)
    0 < tθ ∧ tθ < 1 ∧
      (∫ r, F r ∂Measure.pi (fun _ : Fin N => rawTilt i G b (-θ)))=
        (CommonList.iid (IndependentCounts.bernoulli tθ
          (mass_bounds i G hb (-θ)).1.le (mass_bounds i G hb (-θ)).2.1.le) N).expect (fun low =>
          (CommonList.iid EntrySignFiber.fairSign N).expect (fun sign =>
            ∫ B : Fin N → ℝ, F (fun j => EntrySignFiber.rawRowPoint
              (EntrySignFiber.tag (low j,sign j),B j))
              ∂Measure.pi (fun _ : Fin N => Lθ))) := by
  refine ⟨(mass_bounds i G hb (-θ)).1,(mass_bounds i G hb (-θ)).2.1,?_⟩
  rw [show Measure.pi (fun _ : Fin N => rawTilt i G b (-θ))=
    (Measure.pi (fun _ : Fin N => RawMixedSource.source i G)).tilted
      (fun r => -θ*iidSum (RawMixedSource.demand (xi i) b) N r) from
        pi_tilted_eq_tilted_iidSum _ _ _ N]
  exact integral_actual_tilted_mask_sign i G hb (-θ) N F hF hbound

end FCAppendix.Affine.Uniform06.EntryRawTiltedFiber
