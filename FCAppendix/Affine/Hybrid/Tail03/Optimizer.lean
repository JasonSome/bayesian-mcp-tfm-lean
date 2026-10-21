import FCAppendix.Affine.Hybrid.Tail03.Moments

noncomputable section
namespace FCAppendix.Affine.Hybrid.Tail03
open Set Filter Topology
open scoped BigOperators

structure BoundaryTaylorData (p : Center) (rect : Rectangle p)
    extends LeadingWindow p rect where
  V0 : ℝ
  error : ℝ
  V0_pos : 0< V0
  error_nonneg : 0≤ error
  response : (Fin 2 → ℝ) → ℝ → ℝ
  response_mem : ∀ lam∈rect.box, ∀ v,V0≤ v → response lam v∈Ioo (1:ℝ) (B p)
  response_optimal : ∀ lam∈rect.box, ∀ v,V0≤ v → ∀ b∈Icc (1:ℝ) (B p),
    utility p lam v b≤ utility p lam v (response lam v)
  response_unique : ∀ lam∈rect.box, ∀ v,V0≤ v → ∀ b∈Icc (1:ℝ) (B p),
    utility p lam v b=utility p lam v (response lam v) → b=response lam v
  response_first_order : ∀ lam∈rect.box, ∀ v,V0≤ v →
    v*served1 p lam (response lam v)=payment1 p lam (response lam v)
  optimizer_error : ∀ lam∈rect.box, ∀ v,V0≤ v →
    |response lam v-(B p-1/(2*leadingA p lam*v))|≤ error/v^2
  cost_error : ∀ lam∈rect.box, ∀ v,V0≤ v →
    |(v-utility p lam v (response lam v))-(B p-1/(4*leadingA p lam*v))|≤ error/v^2

lemma stationary_point_unique_max {a b : ℝ} (hab : a< b)
    (f f1 f2 : ℝ → ℝ)
    (hd : ∀ x∈Icc a b,HasDerivAt f (f1 x) x)
    (hd1 : ∀ x∈Icc a b,HasDerivAt f1 (f2 x) x)
    (hn : ∀ x∈Icc a b,f2 x<0) (ha : 0< f1 a) (hb : f1 b<0) :
    ∃ c∈Ioo a b,f1 c=0 ∧
      (∀ x∈Icc a b,f x≤ f c) ∧
      (∀ x∈Icc a b,f x=f c → x=c) := by
  have hcont : ContinuousOn f (Icc a b) := fun x hx => (hd x hx).continuousAt.continuousWithinAt
  have hcont1 : ContinuousOn f1 (Icc a b) := fun x hx => (hd1 x hx).continuousAt.continuousWithinAt
  have hanti : StrictAntiOn f1 (Icc a b) := by
    intro x hx y hy hxy
    have hc : ContinuousOn f1 (Icc x y) := hcont1.mono (Icc_subset_Icc hx.1 hy.2)
    obtain ⟨z,hz,hzder⟩ := exists_hasDerivAt_eq_slope f1 f2 hxy hc
      (fun z hz => hd1 z ⟨hx.1.trans hz.1.le,hz.2.le.trans hy.2⟩)
    have hneg := hn z ⟨hx.1.trans hz.1.le,hz.2.le.trans hy.2⟩
    have hs : (f1 y-f1 x)/(y-x)<0 := hzder ▸ hneg
    have hdxy : 0< y-x := sub_pos.mpr hxy
    have := (div_lt_iff₀ hdxy).mp hs
    linarith
  obtain ⟨c,hc,hc0⟩ := intermediate_value_Icc' hab.le hcont1 ⟨hb.le,ha.le⟩
  have hca : a< c := by
    apply lt_of_le_of_ne hc.1
    intro hac
    subst c
    linarith
  have hcb : c< b := by
    apply lt_of_le_of_ne hc.2
    intro hcb
    subst c
    linarith
  have hstrict : ∀ x∈Icc a b,x≠c → f x< f c := by
    intro x hx hxc
    rcases lt_or_gt_of_ne hxc with hlt | hgt
    · obtain ⟨z,hz,hzd⟩ := exists_hasDerivAt_eq_slope f f1 hlt
        (hcont.mono (Icc_subset_Icc hx.1 hc.2))
        (fun z hz => hd z ⟨hx.1.trans hz.1.le,hz.2.le.trans hc.2⟩)
      have hp : 0< f1 z := by
        have hh := hanti ⟨hx.1.trans hz.1.le,hz.2.le.trans hc.2⟩ hc hz.2
        simpa [hc0] using hh
      rw [hzd] at hp
      have hdiff := (div_pos_iff_of_pos_right (sub_pos.mpr hlt)).mp hp
      linarith
    · obtain ⟨z,hz,hzd⟩ := exists_hasDerivAt_eq_slope f f1 hgt
        (hcont.mono (Icc_subset_Icc hc.1 hx.2))
        (fun z hz => hd z ⟨hc.1.trans hz.1.le,hz.2.le.trans hx.2⟩)
      have hn : f1 z<0 := by
        have hh := hanti hc ⟨hc.1.trans hz.1.le,hz.2.le.trans hx.2⟩ hz.1
        simpa [hc0] using hh
      rw [hzd] at hn
      have hdiff := (div_lt_iff₀ (sub_pos.mpr hgt)).mp hn
      linarith
  refine ⟨c,⟨hca,hcb⟩,hc0,?_,?_⟩
  · intro x hx
    by_cases hxc : x=c
    · simp [hxc]
    · exact (hstrict x hx hxc).le
  · intro x hx heq
    by_contra hxc
    exact (hstrict x hx hxc).ne heq

lemma compact_positive_lower {α : Type*} [TopologicalSpace α]
    {s : Set α} (hs : IsCompact s) {f : α → ℝ}
    (hf : ContinuousOn f s) (hp : ∀ x∈s,0< f x) :
    ∃ a>0,∀ x∈s,a≤ f x := hs.exists_forall_le' hf hp

lemma compact_abs_bound {α : Type*} [TopologicalSpace α]
    {s : Set α} (hs : IsCompact s) {f : α → ℝ}
    (hf : ContinuousOn f s) : ∃ C>0,∀ x∈s,|f x|≤ C := by
  obtain ⟨C,hC⟩ := hs.bddAbove_image hf.abs
  refine ⟨max C 1,lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (le_max_right _ _),?_⟩
  intro x hx
  exact (hC ⟨x,hx,rfl⟩).trans (le_max_left _ _)

theorem uniform_floor_threshold (p : Center) (rect : Rectangle p)
    (h : RectangleAnalyticCertificate p rect) :
    ∃ V0>0, ∀ lam∈rect.box, ∀ v,V0≤ v →
      ∃ b∈Ioo (1:ℝ) (B p),v*served1 p lam b=payment1 p lam b ∧
        (∀ c∈Icc (1:ℝ) (B p),utility p lam v c≤ utility p lam v b) ∧
        (∀ c∈Icc (1:ℝ) (B p),utility p lam v c=utility p lam v b → c=b) := by
  have hs1 : ContinuousOn (fun lam => served1 p lam 1) rect.box := by
    intro lam hlam
    have hc := (derivative_continuity p lam 1 (by norm_num)).1
    have hm : ContinuousAt (fun lam : Fin 2 → ℝ => (lam,(1:ℝ))) lam := by fun_prop
    exact (hc.comp_of_eq hm rfl).continuousWithinAt
  obtain ⟨s0,hs0,hs⟩ := compact_positive_lower rect.isCompact_box hs1
    (fun lam hlam => h.derivative.served_pos lam hlam 1 ⟨le_rfl,B_gt_one p⟩)
  have hp1 : ContinuousOn (fun lam => payment1 p lam 1) rect.box := by
    intro lam hlam
    have hc := (derivative_continuity p lam 1 (by norm_num)).2.2.1
    have hm : ContinuousAt (fun lam : Fin 2 → ℝ => (lam,(1:ℝ))) lam := by fun_prop
    exact (hc.comp_of_eq hm rfl).continuousWithinAt
  obtain ⟨C1,hC1,hC1b⟩ := compact_abs_bound rect.isCompact_box hp1
  have hp2 : ContinuousOn (fun z : (Fin 2 → ℝ)×ℝ => payment2 p z.1 z.2)
      (rect.box×ˢIcc (1:ℝ) (B p)) := by
    intro z hz
    exact (derivative_continuity p z.1 z.2
      (ne_of_gt (by linarith [hz.2.1]))).2.2.2.continuousWithinAt
  obtain ⟨C2,hC2,hC2b⟩ := compact_abs_bound (rect.isCompact_box.prod isCompact_Icc) hp2
  obtain ⟨c,hc,hcurv⟩ := h.derivative.curvature
  have htheta : 0< p.theta := p.theta_pos
  let V0 : ℝ := 1+(C1+1)/s0+(C2+1)/(c*p.theta)
  have hV : 0< V0 := by dsimp [V0]; positivity
  refine ⟨V0,hV,?_⟩
  intro lam hlam v hv
  have hv0 : 0< v := hV.trans_le hv
  have hv1 : C1+1< v*s0 := by
    have hbase : (C1+1)/s0< V0 := by
      have hp : 0<(C2+1)/(c*p.theta) := by positivity
      dsimp [V0]
      linarith
    have hh := (div_lt_iff₀ hs0).mp (hbase.trans_le hv)
    nlinarith
  have hv2 : C2+1< v*(c*p.theta) := by
    have hbase : (C2+1)/(c*p.theta)< V0 := by
      have hp : 0<(C1+1)/s0 := by positivity
      dsimp [V0]
      linarith
    have hh := (div_lt_iff₀ (mul_pos hc p.theta_pos)).mp (hbase.trans_le hv)
    nlinarith
  have hfirst : 0< v*served1 p lam 1-payment1 p lam 1 := by
    have hh := mul_le_mul_of_nonneg_left (hs lam hlam) hv0.le
    have hp := (abs_le.mp (hC1b lam hlam)).2
    nlinarith
  have hsecond : ∀ b∈Icc (1:ℝ) (B p),
      v*served2 p lam b-payment2 p lam b<0 := by
    intro b hb
    have hh := mul_le_mul_of_nonneg_left (hcurv lam hlam b hb) hv0.le
    have hp := (abs_le.mp (hC2b (lam,b) ⟨hlam,hb⟩)).1
    nlinarith
  have hb : v*served1 p lam (B p)-payment1 p lam (B p)<0 := by
    rw [(derivatives_at_B p lam).1,(derivatives_at_B p lam).2]
    norm_num
  obtain ⟨b,hb,hfo,hopt,huniq⟩ := stationary_point_unique_max (B_gt_one p)
    (utility p lam v) (fun b => v*served1 p lam b-payment1 p lam b)
    (fun b => v*served2 p lam b-payment2 p lam b)
    (fun b hb => utility_hasDerivAt p lam v (ne_of_gt (by linarith [hb.1])))
    (fun b hb => ((served1_hasDerivAt p lam (ne_of_gt (by linarith [hb.1]))).const_mul v).sub
      (payment1_hasDerivAt p lam (ne_of_gt (by linarith [hb.1])))) hsecond hfirst hb
  exact ⟨b,hb,sub_eq_zero.mp hfo,hopt,huniq⟩

theorem bulk_floor_widths (p : Center) (rect : Rectangle p)
    (h : RectangleAnalyticCertificate p rect) :
    ∃ w0>0, ∀ w,0< w → w≤ w0 → ∀ lam∈rect.box,
      ∀ v∈Icc (bulkValue p-w) (bulkValue p+w),
        (∀ b∈Icc (1:ℝ) (B p),utility p lam v b≤ utility p lam v 1) ∧
        (∀ b∈Icc (1:ℝ) (B p),utility p lam v b=utility p lam v 1 → b=1) ∧
        (∀ b∈Icc (1:ℝ) (B p),deriv (utility p lam v) b≤-(1/25:ℝ)) := by
  have hc : ContinuousOn (fun lam => served1 p lam 1) rect.box := by
    intro lam hlam
    have hm : ContinuousAt (fun lam : Fin 2 → ℝ => (lam,(1:ℝ))) lam := by fun_prop
    exact ((derivative_continuity p lam 1 (by norm_num)).1.comp_of_eq hm rfl).continuousWithinAt
  obtain ⟨C,hC,hCb⟩ := compact_abs_bound rect.isCompact_box hc
  let w0 : ℝ := min (bulkValue p/2) (1/(20*C))
  have hva : 0< bulkValue p := by linarith [h.central.bulk_large]
  have hw0 : 0< w0 := lt_min (by positivity) (by positivity)
  refine ⟨w0,hw0,?_⟩
  intro w hw hww lam hlam v hv
  have hwv : w≤ bulkValue p/2 := hww.trans (min_le_left _ _)
  have hwC : w*C≤1/20 := by
    have hh := hww.trans (min_le_right _ _)
    exact (le_div_iff₀ (by positivity : 0<20*C)).mp hh |> fun hh => by nlinarith
  have hv0 : 0< v := by linarith [hv.1]
  obtain ⟨c,hc,hcurv⟩ := h.derivative.curvature
  have hsanti : AntitoneOn (served1 p lam) (Icc (1:ℝ) (B p)) := by
    intro a ha b hb hab
    rcases hab.eq_or_lt with heq | hlt
    · simp [heq]
    · obtain ⟨z,hz,hzd⟩ := exists_hasDerivAt_eq_slope (served1 p lam) (served2 p lam) hlt
        (fun z hz => (served1_hasDerivAt p lam (ne_of_gt (by linarith [ha.1,hz.1]))).continuousAt.continuousWithinAt)
        (fun z hz => served1_hasDerivAt p lam (ne_of_gt (by linarith [ha.1,hz.1])))
      have hn : served2 p lam z<0 := by
        have hg := hcurv lam hlam z ⟨ha.1.trans hz.1.le,hz.2.le.trans hb.2⟩
        have hp := mul_pos hc p.theta_pos
        linarith
      rw [hzd] at hn
      have hh := (div_lt_iff₀ (sub_pos.mpr hlt)).mp hn
      linarith
  have hderbound : ∀ b∈Icc (1:ℝ) (B p),v*served1 p lam b-payment1 p lam b≤-(1/25:ℝ) := by
    intro b hb
    have hsf := hsanti ⟨le_rfl,(B_gt_one p).le⟩ hb hb.1
    have hm := mul_le_mul_of_nonneg_left hsf hv0.le
    have hs0 := (hCb lam hlam)
    have hspos := h.derivative.served_pos lam hlam 1 ⟨le_rfl,B_gt_one p⟩
    have hhigh := mul_le_mul_of_nonneg_right hv.2 hspos.le
    have hwidth := mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) hs0) hw.le
    have hbulk := h.derivative.bulk lam hlam
    have hpay := h.derivative.payment_pos lam hlam b hb
    nlinarith only [hm,hhigh,hwidth,hbulk,hpay,hwC]
  have hderneg (b : ℝ) (hb : b∈Icc (1:ℝ) (B p)) :
      v*served1 p lam b-payment1 p lam b<0 :=
    (hderbound b hb).trans_lt (by norm_num)
  have hstrict : ∀ b∈Icc (1:ℝ) (B p),1< b → utility p lam v b< utility p lam v 1 := by
    intro b hb hgt
    obtain ⟨z,hz,hzd⟩ := exists_hasDerivAt_eq_slope (utility p lam v)
      (fun b => v*served1 p lam b-payment1 p lam b) hgt
      (fun z hz => (utility_hasDerivAt p lam v (ne_of_gt (by linarith [hz.1]))).continuousAt.continuousWithinAt)
      (fun z hz => utility_hasDerivAt p lam v (ne_of_gt (by linarith [hz.1])))
    have hn := hderneg z ⟨hz.1.le,hz.2.le.trans hb.2⟩
    rw [hzd] at hn
    have hh := (div_lt_iff₀ (sub_pos.mpr hgt)).mp hn
    linarith
  constructor
  · intro b hb
    rcases hb.1.eq_or_lt with heq | hgt
    · simp [←heq]
    · exact (hstrict b hb hgt).le
  · constructor
    · intro b hb heq
      by_contra hn
      have hgt : 1< b := lt_of_le_of_ne hb.1 (Ne.symm hn)
      exact (hstrict b hb hgt).ne heq
    · intro b hb
      rw [(utility_hasDerivAt p lam v (ne_of_gt (by linarith [hb.1]))).deriv]
      exact hderbound b hb

end FCAppendix.Affine.Hybrid.Tail03
