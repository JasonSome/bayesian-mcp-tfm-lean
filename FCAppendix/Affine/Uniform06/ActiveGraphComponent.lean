import FCAppendix.Affine.Uniform06.LowChernoffSource
import FCAppendix.Affine.Uniform07.RateDefinitions
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Topology.Order.IntermediateValue

noncomputable section

namespace FCAppendix.Affine.Uniform06.ActiveGraphComponent

open MeasureTheory Set Filter
open FCAppendix.Affine.Uniform07 FCAppendix.Affine.ClippedResidual

section Graph

variable {Ω : Type*} [MeasurableSpace Ω]

theorem graph_image_component
    (μ : Measure Ω) {V X : Ω → ℝ} (hV : Measurable V) (hX : Measurable X)
    {s J : Set ℝ} (hs : MeasurableSet s) (_hJ : MeasurableSet J)
    {f : ℝ → ℝ} (hf : Measurable f) {K : NNReal}
    (hLip : LipschitzOnWith K f s)
    (hvalue : volume.restrict s ≪ μ.map V)
    (hgraph : ∀ᵐ ω ∂μ, V ω ∈ s → X ω = f (V ω))
    (hcover : J ⊆ f '' s) : volume.restrict J ≪ μ.map X := by
  have hnull (E : Set ℝ) (hE : MeasurableSet E) (hEX : μ.map X E = 0) :
      (volume.restrict J) E = 0 := by
    let T : Set ℝ := f ⁻¹' E ∩ s
    have hTm : MeasurableSet T := (hE.preimage hf).inter hs
    have hTs : T ⊆ s := inter_subset_right
    have hEX' : μ (X ⁻¹' E) = 0 := by rwa [Measure.map_apply hX hE] at hEX
    have hinc : ∀ᵐ ω ∂μ, ω ∈ V ⁻¹' T → ω ∈ X ⁻¹' E := by
      filter_upwards [hgraph] with ω hω hT
      have hv : f (V ω) ∈ E ∧ V ω ∈ s := hT
      simpa only [mem_preimage, hω hv.2] using hv.1
    have hTV : μ.map V T = 0 := by
      rw [Measure.map_apply hV hTm]
      exact le_antisymm ((measure_mono_ae hinc).trans_eq hEX') zero_le
    have hT0 : volume T = 0 := by
      have hh := hvalue hTV
      rwa [Measure.restrict_apply hTm, inter_eq_self_of_subset_left hTs] at hh
    have himage0 : volume (f '' T) = 0 := by
      have hh := (hLip.mono hTs).hausdorffMeasure_image_le
        (show (0 : ℝ) ≤ 1 by norm_num)
      apply le_antisymm _ zero_le
      convert! hh using 1 <;> first | rfl | simp only [hausdorffMeasure_real, hT0, mul_zero]
    have hsubset : E ∩ J ⊆ f '' T := by
      rintro y ⟨hyE,hyJ⟩
      obtain ⟨v,hvs,hvy⟩ := hcover hyJ
      refine ⟨v,⟨?_,hvs⟩,hvy⟩
      simpa only [mem_preimage,hvy] using hyE
    rw [Measure.restrict_apply hE]
    exact measure_mono_null hsubset himage0
  intro E hE
  obtain ⟨A,hEA,hAm,hAX⟩ := exists_measurable_superset_of_null hE
  exact measure_mono_null hEA (hnull A hAm hAX)

theorem uniform_marginal_local_component
    (μ : Measure Ω) (V : Ω → ℝ) {c t a b : ℝ} (hc : 0 < c)
    (hvalue : μ.map V = ENNReal.ofReal c • volume.restrict (Icc (0:ℝ) t))
    (ha : 0 ≤ a) (hbt : b ≤ t) :
    volume.restrict (Icc a b) ≪ μ.map V := by
  intro E hE
  have h0 : (volume.restrict (Icc (0:ℝ) t)) E = 0 := by
    rw [hvalue, Measure.smul_apply, smul_eq_mul] at hE
    exact (mul_eq_zero.mp hE).resolve_left
      (ne_of_gt (ENNReal.ofReal_pos.mpr hc))
  have hle : volume.restrict (Icc a b) ≤ volume.restrict (Icc (0:ℝ) t) :=
    Measure.restrict_mono_set volume (Icc_subset_Icc ha hbt)
  exact le_antisymm ((hle E).trans_eq h0) zero_le

end Graph

def reciprocalAffine (C p v : ℝ) : ℝ := C-p/v

theorem measurable_reciprocalAffine (C p : ℝ) : Measurable (reciprocalAffine C p) := by
  unfold reciprocalAffine
  fun_prop

theorem reciprocalAffine_continuousOn {a b : ℝ} (ha : 0 < a) (C p : ℝ) :
    ContinuousOn (reciprocalAffine C p) (Icc a b) := by
  exact continuousOn_const.sub
    (continuousOn_const.div continuousOn_id fun v hv => (ha.trans_le hv.1).ne')

theorem reciprocalAffine_strictMono {a : ℝ} (ha : 0 < a) (C : ℝ)
    {p : ℝ} (hp : 0 < p) : StrictMonoOn (reciprocalAffine C p) (Ici a) := by
  intro v hv w hw hvw
  have h := div_lt_div_of_pos_left hp (ha.trans_le hv) hvw
  dsimp [reciprocalAffine]
  linarith

theorem reciprocalAffine_lipschitz {a p : ℝ} (ha : 0 < a) (hp : 0 ≤ p)
    (C : ℝ) :
    LipschitzOnWith (Real.toNNReal (p/(a*a))) (reciprocalAffine C p) (Ici a) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro v hv w hw
  have hv0 := ha.trans_le hv
  have hw0 := ha.trans_le hw
  have haa : 0 < a*a := mul_pos ha ha
  have hvw : 0 < v*w := mul_pos hv0 hw0
  have hden : a*a ≤ v*w := mul_le_mul hv hw ha.le hv0.le
  have hconst : 0 ≤ p/(a*a) := div_nonneg hp haa.le
  rw [Real.coe_toNNReal _ hconst, Real.dist_eq, Real.dist_eq]
  have he : reciprocalAffine C p v-reciprocalAffine C p w =
      p*(v-w)/(v*w) := by
    unfold reciprocalAffine
    field_simp [hv0.ne',hw0.ne']
    ring
  rw [he, abs_div, abs_mul, abs_of_nonneg hp, abs_of_pos hvw]
  calc
    p*|v-w| /(v*w) ≤ p*|v-w| /(a*a) :=
      div_le_div_of_nonneg_left (mul_nonneg hp (abs_nonneg _)) haa hden
    _ = p/(a*a)*|v-w| := by ring

theorem reciprocal_graph_component
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {V X : Ω → ℝ} (hV : Measurable V) (hX : Measurable X)
    {a b C p c t : ℝ} (ha : 0 < a) (hab : a < b) (hbt : b ≤ t)
    (hp : 0 < p) (hc : 0 < c)
    (hvalue : μ.map V = ENNReal.ofReal c • volume.restrict (Icc (0:ℝ) t))
    (hgraph : ∀ᵐ ω ∂μ, V ω ∈ Icc a b → X ω = reciprocalAffine C p (V ω)) :
    reciprocalAffine C p a < reciprocalAffine C p b ∧
      volume.restrict (Ioo (reciprocalAffine C p a) (reciprocalAffine C p b)) ≪
        μ.map X := by
  have hmono := reciprocalAffine_strictMono ha C hp
  refine ⟨hmono (show a ∈ Ici a by exact le_refl a) (show b ∈ Ici a from hab.le) hab,?_⟩
  apply graph_image_component μ hV hX measurableSet_Icc measurableSet_Ioo
    (measurable_reciprocalAffine C p)
    ((reciprocalAffine_lipschitz ha hp.le C).mono fun _ hv => hv.1)
    (uniform_marginal_local_component μ V hc hvalue ha.le hbt) hgraph
  intro y hy
  exact intermediate_value_Icc hab.le (reciprocalAffine_continuousOn ha C p)
    ⟨hy.1.le,hy.2.le⟩

section LiteralSource

def activeBid (i : Row) (v : ℝ) : ℝ :=
  entry i*v/(kappa i*v+xi i*entry i)

def activeLeft (i : Row) : ℝ := ((3*x i+1)/4)*cutoff i
def activeRight (i : Row) : ℝ := ((x i+1)/2)*cutoff i

def activeDemand (i : Row) (z v : ℝ) : ℝ :=
  reciprocalAffine ((1-z*kappa i/x i)/xi i) (z*cutoff i) v

def originalLowerStatisticLaw (i : Row) (G : Measure (ℝ × ℝ)) (z : ℝ) : Measure ℝ :=
  G.map (fun p => exposure (xi i) (z*cutoff i) p.2)

theorem active_strip_bounds (i : Row) :
    0 < activeLeft i ∧ entry i < activeLeft i ∧
      activeLeft i < activeRight i ∧ activeRight i < cutoff i := by
  have ht := cutoff_pos i
  cases i <;> norm_num [activeLeft,activeRight,entry,x,xQ] at * <;>
    refine ⟨by linarith,by linarith,by linarith,by linarith⟩

theorem activeBid_scaled (i : Row) {y : ℝ} (hy : 0 < y) :
    activeBid i (cutoff i*y) =
      cutoff i*(x i*y/(kappa i*y+xi i*x i)) := by
  have ht := cutoff_pos i
  have hx : 0 < x i := by cases i <;> norm_num [x,xQ]
  have hk : 0 < kappa i := by cases i <;> norm_num [kappa,kappaQ,xiQ,etaQ]
  have hden : 0 < kappa i*y+xi i*x i := add_pos (mul_pos hk hy) (mul_pos (xi_pos i) hx)
  unfold activeBid entry
  rw [show kappa i*(cutoff i*y)+xi i*(x i*cutoff i) =
    cutoff i*(kappa i*y+xi i*x i) by ring]
  field_simp [ht.ne',hden.ne']

theorem exposure_active_normalized (i : Row) {z y : ℝ}
    (hz : z ∈ Icc (1/2:ℝ) (x i)) (hy : y ∈ Icc (x i) 1) :
    exposure (xi i) z (x i*y/(kappa i*y+xi i*x i)) =
      pieceP ((1-z*kappa i/x i)/xi i) z y := by
  have hx : 0 < x i := by cases i <;> norm_num [x,xQ]
  have hxi := xi_pos i
  have hk : 0 < kappa i := by cases i <;> norm_num [kappa,kappaQ,xiQ,etaQ]
  have hsum : kappa i+xi i=1 := by
    cases i <;> norm_num [kappa,kappaQ,xi,xiQ,etaQ]
  have hy0 := hx.trans_le hy.1
  have hden : 0 < kappa i*y+xi i*x i :=
    add_pos (mul_pos hk hy0) (mul_pos hxi hx)
  have hb0 : 0 < x i*y/(kappa i*y+xi i*x i) := div_pos (mul_pos hx hy0) hden
  have hbx : x i ≤ x i*y/(kappa i*y+xi i*x i) := by
    apply (le_div_iff₀ hden).mpr
    have hp := mul_nonneg (mul_nonneg hxi.le hx.le) (sub_nonneg.mpr hy.1)
    have he : x i*y-x i*(kappa i*y+xi i*x i) = xi i*x i*(y-x i) := by
      rw [show kappa i=1-xi i by linarith]
      ring
    rw [← he] at hp
    linarith
  have hbz := hz.2.trans hbx
  have hp := high_piece_bounds i hz.1 hz.2 hy.1 hy.2
  have he : (x i*y/(kappa i*y+xi i*x i)-z)/
      (xi i*(x i*y/(kappa i*y+xi i*x i))) =
      pieceP ((1-z*kappa i/x i)/xi i) z y := by
    unfold pieceP
    field_simp [hden.ne',hx.ne',hy0.ne',hxi.ne']
    ring
  unfold exposure
  rw [max_eq_left hbz, max_eq_right (sub_nonneg.mpr hbz), he, min_eq_right hp.2]

theorem exposure_active_physical (i : Row) {z v : ℝ}
    (hz : z ∈ Icc (1/2:ℝ) (x i)) (hv : v ∈ Icc (entry i) (cutoff i)) :
    exposure (xi i) (z*cutoff i) (activeBid i v) = activeDemand i z v := by
  have ht := cutoff_pos i
  have hx : 0 < x i := by cases i <;> norm_num [x,xQ]
  have he : 0 < entry i := mul_pos hx ht
  have hv0 := he.trans_le hv.1
  have hy0 : 0 < v/cutoff i := div_pos hv0 ht
  have hy : v/cutoff i ∈ Icc (x i) 1 := by
    constructor
    · exact (le_div_iff₀ ht).mpr (by simpa only [entry] using hv.1)
    · exact (div_le_one ht).mpr hv.2
  have hrepr : v = cutoff i*(v/cutoff i) := by field_simp [ht.ne']
  have hbid : activeBid i v = cutoff i*(x i*(v/cutoff i)/
      (kappa i*(v/cutoff i)+xi i*x i)) := by
    calc
      activeBid i v = activeBid i (cutoff i*(v/cutoff i)) := congrArg (activeBid i) hrepr
      _ = _ := activeBid_scaled i hy0
  calc
    exposure (xi i) (z*cutoff i) (activeBid i v) =
        exposure (xi i) z (x i*(v/cutoff i)/
          (kappa i*(v/cutoff i)+xi i*x i)) := by
      rw [hbid,mul_comm z (cutoff i)]
      exact LowChernoff.exposure_positive_scaling (xi_pos i)
        (by linarith [hz.1]) ht
    _ = pieceP ((1-z*kappa i/x i)/xi i) z (v/cutoff i) :=
      exposure_active_normalized i hz hy
    _ = activeDemand i z v := by
      unfold pieceP activeDemand reciprocalAffine
      field_simp [ht.ne',hv0.ne']

theorem original_active_graph_continuous_component (i : Row)
    (G : Measure (ℝ × ℝ))
    (hvalue : G.map Prod.fst = LowChernoff.conditionalValueLaw i)
    (hactive : ∀ᵐ p ∂G, p.1 ∈ Ioc (entry i) (cutoff i) → p.2=activeBid i p.1) :
    ∀ z ∈ Icc (1/2:ℝ) (x i),
      activeDemand i z (activeLeft i) < activeDemand i z (activeRight i) ∧
        volume.restrict (Ioo (activeDemand i z (activeLeft i))
          (activeDemand i z (activeRight i))) ≪ originalLowerStatisticLaw i G z := by
  intro z hz
  have hs := active_strip_bounds i
  have ht := cutoff_pos i
  have hz0 : 0 < z := by linarith [hz.1]
  have hX : Measurable (fun p : ℝ × ℝ => exposure (xi i) (z*cutoff i) p.2) :=
    (continuous_exposure (xi_pos i) (mul_pos hz0 ht)).measurable.comp measurable_snd
  have hgraph : ∀ᵐ p ∂G, p.1 ∈ Icc (activeLeft i) (activeRight i) →
      exposure (xi i) (z*cutoff i) p.2 = activeDemand i z p.1 := by
    filter_upwards [hactive] with p hp hpv
    have hpactive : p.1 ∈ Ioc (entry i) (cutoff i) :=
      ⟨hs.2.1.trans_le hpv.1,hpv.2.trans hs.2.2.2.le⟩
    rw [hp hpactive]
    exact exposure_active_physical i hz ⟨hpactive.1.le,hpactive.2⟩
  exact reciprocal_graph_component G measurable_fst hX hs.1 hs.2.2.1 hs.2.2.2.le
    (mul_pos hz0 ht) (one_div_pos.mpr ht) hvalue hgraph

end LiteralSource

end FCAppendix.Affine.Uniform06.ActiveGraphComponent
