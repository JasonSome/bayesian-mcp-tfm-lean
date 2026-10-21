import FCAppendix.Affine.Hybrid.Tail03.Rectangle

noncomputable section
namespace FCAppendix.Affine.Hybrid.Tail03
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators

def flagShape (p : Center) (b : ℝ) : ℝ := ((B p-b)/width p)^2
def weightedFlagShape (p : Center) (b : ℝ) : ℝ := flagShape p b/b
def momentMap (p : Center) (G : ProbabilityMeasure ℝ) (r : Fin 2) : ℝ :=
  ((1-xi p/2)*(∫ b,mixedProb p r b ∂(G : Measure ℝ))-(xi p/2)*deficit p r)/
    (∫ b,mixedProb p r b/b ∂(G : Measure ℝ))

lemma flagShape_bounds (p : Center) {b : ℝ} (hb : b∈Icc (1:ℝ) (B p)) :
    flagShape p b∈Icc (0:ℝ) 1 ∧ weightedFlagShape p b∈Icc (0:ℝ) 1 := by
  have hd := width_pos p
  have hb0 : 0< b := by linarith [hb.1]
  have hy0 : 0≤(B p-b)/width p := div_nonneg (sub_nonneg.mpr hb.2) hd.le
  have hy1 : (B p-b)/width p≤1 := by
    apply (div_le_one hd).2
    unfold width
    linarith [hb.1]
  have hf : flagShape p b∈Icc (0:ℝ) 1 := by
    unfold flagShape
    exact ⟨sq_nonneg _,by nlinarith⟩
  refine ⟨hf,div_nonneg hf.1 hb0.le,?_⟩
  unfold weightedFlagShape
  exact (div_le_one hb0).2 (hf.2.trans hb.1)

lemma bulk_flagShape_bounds (p : Center) {u b : ℝ} (hu : 0≤ u)
    (hb : b∈Icc (1:ℝ) (B p)) (hbulk : b≤1+u) :
    1-2*u/width p≤ flagShape p b ∧
      1-(2/width p+1)*u≤ weightedFlagShape p b := by
  have hd := width_pos p
  have hb0 : 0< b := by linarith [hb.1]
  have heq : flagShape p b=(1-(b-1)/width p)^2 := by
    unfold flagShape
    congr 1
    have hn : B p-b=width p-(b-1) := by unfold width;ring
    rw [hn]
    field_simp [hd.ne']
  have hy0 : 0≤(b-1)/width p := div_nonneg (sub_nonneg.mpr hb.1) hd.le
  have hyu : (b-1)/width p≤ u/width p :=
    (div_le_div_iff_of_pos_right hd).2 (by linarith)
  have hf : 1-2*u/width p≤ flagShape p b := by
    rw [heq]
    have hquad : 1-2*(u/width p)≤(1-(b-1)/width p)^2 := by
      nlinarith only [hyu,sq_nonneg ((b-1)/width p)]
    convert! hquad using 1 ; ring
  refine ⟨hf,?_⟩
  unfold weightedFlagShape
  apply (le_div_iff₀ hb0).2
  have hu0 : 0≤(2/width p+1)*u := by positivity
  have hmul := mul_nonneg (sub_nonneg.mpr hb.1) hu0
  have hid : (2/width p+1)*u=2*u/width p+u := by ring
  nlinarith only [hf,hmul,hbulk,hid]

lemma integral_near_one {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (f : α → ℝ) (s : Set α)
    (hf : Measurable f) (hs : MeasurableSet s) {d e : ℝ}
    (hd0 : 0≤ d) (hd1 : d≤1) (he0 : 0≤ e)
    (hb : ∀ᵐ x ∂μ,f x∈Icc (0:ℝ) 1)
    (hbulk : ∀ᵐ x ∂μ,x∈s → 1-d≤ f x)
    (hmass : 1-e≤ μ.real s) :
    1-d-e≤∫ x,f x ∂μ ∧ (∫ x,f x ∂μ)≤1 := by
  have hi := Integrable.of_mem_Icc 0 1 hf.aemeasurable hb
  have hi0 : Integrable (s.indicator (fun _ : α => (1-d:ℝ))) μ :=
    (integrable_const _).indicator hs
  have hlo : (1-d)*μ.real s≤∫ x,f x ∂μ := by
    have hh := integral_mono_ae hi0 hi (by
      filter_upwards [hb,hbulk] with x hx hxs
      by_cases hm : x∈s
      · simpa [Set.indicator_of_mem hm] using hxs hm
      · simpa [Set.indicator_of_notMem hm] using hx.1)
    simpa [integral_indicator_const,hs,smul_eq_mul,mul_comm] using hh
  have hprod := mul_le_mul_of_nonneg_left hmass (sub_nonneg.mpr hd1)
  have hde : 0≤ d*e := mul_nonneg hd0 he0
  have hup := integral_mono_ae hi (integrable_const (1:ℝ)) (hb.mono fun _ h => h.2)
  exact ⟨by nlinarith,by simpa using hup⟩

lemma normalized_momentMap (p : Center) (G : ProbabilityMeasure ℝ)
    (hsupport : ∀ᵐ b ∂(G : Measure ℝ),b∈Icc (1:ℝ) (B p)) (r : Fin 2) :
    momentMap p G r=
      ((1-xi p/2)*(∫ b,flagShape p b ∂(G : Measure ℝ))-
        (xi p/2)*(2*q0 r-1))/(∫ b,weightedFlagShape p b ∂(G : Measure ℝ)) := by
  have hm0 : Measurable (flagShape p) := by unfold flagShape; fun_prop
  have hm1 : Measurable (weightedFlagShape p) := by unfold weightedFlagShape; fun_prop
  have hi0 := Integrable.of_mem_Icc 0 1 hm0.aemeasurable
    (hsupport.mono fun _ hb => (flagShape_bounds p hb).1)
  have hi1 := Integrable.of_mem_Icc 0 1 hm1.aemeasurable
    (hsupport.mono fun _ hb => (flagShape_bounds p hb).2)
  have h0 : (∫ b,mixedProb p r b ∂(G : Measure ℝ))=
      e0 p r*(∫ b,flagShape p b ∂(G : Measure ℝ)) := by
    exact integral_const_mul _ _
  have h1 : (∫ b,mixedProb p r b/b ∂(G : Measure ℝ))=
      e0 p r*(∫ b,weightedFlagShape p b ∂(G : Measure ℝ)) := by
    calc
      _ = ∫ b,e0 p r*weightedFlagShape p b ∂(G : Measure ℝ) := by
        congr 1
        ext b
        unfold mixedProb weightedFlagShape flagShape
        ring
      _ = _ := integral_const_mul _ _
  have he := (e0_pos p r).ne'
  have hdelta : deficit p r=e0 p r*(2*q0 r-1) := by
    have hi := deficit_div_e0 p r
    nlinarith [(div_eq_iff he).mp hi]
  unfold momentMap
  rw [h0,h1,hdelta]
  by_cases hg : (∫ b,weightedFlagShape p b ∂(G : Measure ℝ))=0
  · simp [hg]
  · field_simp [he,hg]

lemma momentMap_error (p : Center) (G : ProbabilityMeasure ℝ)
    {u zeta E : ℝ} (hu : 0≤ u) (hz : 0≤ zeta)
    (hE : E=(2/width p+1)*u+2*zeta) (hEsmall : E≤1/2)
    (hsupport : ∀ᵐ b ∂(G : Measure ℝ),b∈Icc (1:ℝ) (B p))
    (hbulk : 1-2*zeta≤(G : Measure ℝ).real (Icc 1 (1+u))) :
    (∀ r,e0 p r/2≤∫ b,mixedProb p r b/b ∂(G : Measure ℝ)) ∧
      ∀ r,|momentMap p G r-lambda0 p r|≤4*E := by
  have hwidth := width_pos p
  let d : ℝ := (2/width p+1)*u
  have hd0 : 0≤ d := by dsimp [d]; have := width_pos p; positivity
  have hE0 : 0≤ E := by rw [hE]; positivity
  have hdE : d≤ E := by rw [hE]; dsimp [d]; linarith
  have hd1 : d≤1 := by linarith
  have hm0 : Measurable (flagShape p) := by unfold flagShape; fun_prop
  have hm1 : Measurable (weightedFlagShape p) := by unfold weightedFlagShape; fun_prop
  have hfg : ∀ᵐ b ∂(G : Measure ℝ),
      flagShape p b∈Icc (0:ℝ) 1 ∧ weightedFlagShape p b∈Icc (0:ℝ) 1 :=
    hsupport.mono fun _ hb => flagShape_bounds p hb
  have hfl : ∀ᵐ b ∂(G : Measure ℝ),b∈Icc 1 (1+u) → 1-d≤ flagShape p b := by
    filter_upwards [hsupport] with b hb hbulk
    have hh := (bulk_flagShape_bounds p hu hb hbulk.2).1
    have hu0 : 0≤ u := hu
    dsimp [d]
    have hid : (2/width p+1)*u=2*u/width p+u := by ring
    linarith only [hh,hu0,hid]
  have hgl : ∀ᵐ b ∂(G : Measure ℝ),b∈Icc 1 (1+u) → 1-d≤ weightedFlagShape p b := by
    filter_upwards [hsupport] with b hb hbulk
    exact (bulk_flagShape_bounds p hu hb hbulk.2).2
  have hf := integral_near_one (G : Measure ℝ) (flagShape p) (Icc 1 (1+u))
    hm0 measurableSet_Icc hd0 hd1 (by positivity : 0≤2*zeta)
    (hfg.mono fun _ hb => hb.1) hfl hbulk
  have hg := integral_near_one (G : Measure ℝ) (weightedFlagShape p) (Icc 1 (1+u))
    hm1 measurableSet_Icc hd0 hd1 (by positivity : 0≤2*zeta)
    (hfg.mono fun _ hb => hb.2) hgl hbulk
  let f := ∫ b,flagShape p b ∂(G : Measure ℝ)
  let g := ∫ b,weightedFlagShape p b ∂(G : Measure ℝ)
  have hf0 : 1-E≤ f := by dsimp [f]; rw [hE]; dsimp [d] at hf; linarith [hf.1]
  have hg0 : 1-E≤ g := by dsimp [g]; rw [hE]; dsimp [d] at hg; linarith [hg.1]
  have hgp : 0< g := by linarith
  have hgHalf : 1/2≤ g := by linarith
  have hg1 : g≤1 := hg.2
  have hf1 : f≤1 := hf.2
  constructor
  · intro r
    calc
      e0 p r/2 ≤ e0 p r*g := by nlinarith [e0_pos p r]
      _ = ∫ b,mixedProb p r b/b ∂(G : Measure ℝ) := by
        rw [←integral_const_mul]
        congr 1
        ext b
        unfold mixedProb weightedFlagShape flagShape
        ring
  · intro r
    rw [normalized_momentMap p G hsupport r]
    change |((1-xi p/2)*f-(xi p/2)*(2*q0 r-1))/g-lambda0 p r|≤4*E
    have hb0 : 0≤1-xi p/2 := by linarith [xi_lt_half p]
    have hb1 : 1-xi p/2≤1 := by linarith [xi_pos p]
    have hl0 : 0≤ lambda0 p r := by
      unfold lambda0
      have hq : q0 r≤1 := by fin_cases r <;> norm_num [q0]
      nlinarith [xi_pos p,xi_lt_half p]
    have hl1 : lambda0 p r≤1 := by
      unfold lambda0
      have hq : 0≤ q0 r := by fin_cases r <;> norm_num [q0]
      nlinarith [xi_pos p]
    have hid : (1-xi p/2)*f-(xi p/2)*(2*q0 r-1)=
        lambda0 p r+(1-xi p/2)*(f-1) := by unfold lambda0; ring
    rw [hid,abs_le]
    have hbf : -(E)≤(1-xi p/2)*(f-1) := by
      have h1 := mul_nonneg hb0 (sub_nonneg.mpr hf0)
      have h2 := mul_nonneg hE0 (sub_nonneg.mpr hb1)
      nlinarith
    have hbf0 : (1-xi p/2)*(f-1)≤0 :=
      mul_nonpos_of_nonneg_of_nonpos hb0 (by linarith)
    have hlg0 : 0≤ lambda0 p r*(1-g) := mul_nonneg hl0 (by linarith)
    have hlgE : lambda0 p r*(1-g)≤ E := by
      have h1 := mul_nonneg hl0 (by linarith : 0≤ E-(1-g))
      have h2 := mul_nonneg hE0 (sub_nonneg.mpr hl1)
      nlinarith
    have hEg := mul_nonneg hE0 (sub_nonneg.mpr hgHalf)
    constructor
    · rw [le_sub_iff_add_le]
      apply (le_div_iff₀ hgp).2
      nlinarith
    · rw [sub_le_iff_le_add]
      apply (div_le_iff₀ hgp).2
      nlinarith

structure ExplicitMomentRectangleInequalities (p : Center) (rect : Rectangle p)
    (u zeta : ℝ) : Prop where
  u_pos : 0< u
  u_lt_width : u< width p
  zeta_pos : 0< zeta
  zeta_small : zeta<1/100
  denominator : ∀ G : ProbabilityMeasure ℝ,
    (∀ᵐ b ∂(G : Measure ℝ),b∈Icc (1:ℝ) (B p)) →
    1-2*zeta≤(G : Measure ℝ).real (Icc 1 (1+u)) →
    ∀ r,e0 p r/2≤∫ b,mixedProb p r b/b ∂(G : Measure ℝ)
  invariant : ∀ G : ProbabilityMeasure ℝ,
    (∀ᵐ b ∂(G : Measure ℝ),b∈Icc (1:ℝ) (B p)) →
    1-2*zeta≤(G : Measure ℝ).real (Icc 1 (1+u)) →
    momentMap p G∈rect.box

theorem positive_bulk_forces_rectangle_invariance (p : Center) (rect : Rectangle p) :
    ∃ u zeta : ℝ,ExplicitMomentRectangleInequalities p rect u zeta := by
  let r : ℝ := min (min (lambda0 p 0-rect.lo 0) (rect.hi 0-lambda0 p 0))
    (min (lambda0 p 1-rect.lo 1) (rect.hi 1-lambda0 p 1))
  have hr : 0< r := by
    dsimp [r]
    exact lt_min (lt_min (sub_pos.mpr (rect.center_interior 0).1)
      (sub_pos.mpr (rect.center_interior 0).2))
      (lt_min (sub_pos.mpr (rect.center_interior 1).1)
        (sub_pos.mpr (rect.center_interior 1).2))
  have hrlo (i : Fin 2) : r≤ lambda0 p i-rect.lo i := by
    fin_cases i
    · exact (min_le_left _ _).trans (min_le_left _ _)
    · exact (min_le_right _ _).trans (min_le_left _ _)
  have hrhi (i : Fin 2) : r≤ rect.hi i-lambda0 p i := by
    fin_cases i
    · exact (min_le_left _ _).trans (min_le_right _ _)
    · exact (min_le_right _ _).trans (min_le_right _ _)
  let eps : ℝ := min (r/8) (1/8)
  let C : ℝ := 2/width p+1
  let u : ℝ := min (width p/2) (eps/(4*C))
  let zeta : ℝ := min (1/200) (eps/16)
  let E : ℝ := C*u+2*zeta
  have heps : 0< eps := lt_min (by positivity) (by norm_num)
  have hC : 0< C := by dsimp [C]; have := width_pos p; positivity
  have hu : 0< u := lt_min (by have := width_pos p; positivity) (by positivity)
  have hz : 0< zeta := lt_min (by norm_num) (by positivity)
  have hCu : C*u≤ eps/4 := by
    have hh : u≤ eps/(4*C) := min_le_right _ _
    have hh' := (le_div_iff₀ (show 0<4*C by positivity)).mp hh
    nlinarith
  have hzE : zeta≤ eps/16 := min_le_right _ _
  have hEs : E≤1/2 := by
    have he := min_le_right (r/8) (1/8)
    dsimp [E]
    nlinarith
  have hEr : 4*E< r := by
    have he := min_le_left (r/8) (1/8)
    dsimp [E]
    nlinarith
  have hEeq : E=(2/width p+1)*u+2*zeta := rfl
  refine ⟨u,zeta,{
    u_pos := hu
    u_lt_width := (min_le_left _ _).trans_lt (by have := width_pos p; linarith)
    zeta_pos := hz
    zeta_small := (min_le_left _ _).trans_lt (by norm_num)
    denominator := fun G hs hb => (momentMap_error p G hu.le hz.le hEeq hEs hs hb).1
    invariant := ?_ }⟩
  intro G hs hb
  have hh := (momentMap_error p G hu.le hz.le hEeq hEs hs hb).2
  constructor <;> intro i
  · have h := (abs_le.mp (hh i)).1
    nlinarith [hrlo i]
  · have h := (abs_le.mp (hh i)).2
    nlinarith [hrhi i]

end FCAppendix.Affine.Hybrid.Tail03
