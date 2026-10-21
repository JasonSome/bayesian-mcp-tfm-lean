import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Sequences

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.SelectedMaximumDerivative

open Set Filter Topology

theorem ordered_slope_bound
    (F D : ℝ → ℝ → ℝ) (V : ℝ → ℝ)
    {a b u v d ε : ℝ} (hab : a < b)
    (hVa : V a=F u a) (hVb : V b=F v b)
    (hmaxa : F v a ≤ V a) (hmaxb : F u b ≤ V b)
    (hder : ∀ w : ℝ, w=u ∨ w=v → ∀ z ∈ Icc a b,
      HasDerivAt (F w) (D w z) z)
    (hbound : ∀ w : ℝ, w=u ∨ w=v → ∀ z ∈ Icc a b,
      |D w z-d| ≤ ε) :
    |(V b-V a)/(b-a)-d| ≤ ε := by
  have hcont (w : ℝ) (hw : w=u ∨ w=v) : ContinuousOn (F w) (Icc a b) :=
    fun z hz => (hder w hw z hz).continuousAt.continuousWithinAt
  obtain ⟨s,hs,hds⟩ := exists_hasDerivAt_eq_slope (F u) (D u) hab
    (hcont u (Or.inl rfl))
    (fun z hz => hder u (Or.inl rfl) z ⟨hz.1.le,hz.2.le⟩)
  obtain ⟨t,ht,hdt⟩ := exists_hasDerivAt_eq_slope (F v) (D v) hab
    (hcont v (Or.inr rfl))
    (fun z hz => hder v (Or.inr rfl) z ⟨hz.1.le,hz.2.le⟩)
  have hleft : D u s ≤ (V b-V a)/(b-a) := by
    rw [hds]
    apply div_le_div_of_nonneg_right _ (sub_pos.mpr hab).le
    rw [hVa]
    linarith
  have hright : (V b-V a)/(b-a) ≤ D v t := by
    rw [hdt]
    apply div_le_div_of_nonneg_right _ (sub_pos.mpr hab).le
    rw [hVb]
    linarith
  have hbs := abs_le.mp (hbound u (Or.inl rfl) s ⟨hs.1.le,hs.2.le⟩)
  have hbt := abs_le.mp (hbound v (Or.inr rfl) t ⟨ht.1.le,ht.2.le⟩)
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem hasDerivWithinAt_selected_max
    (F D : ℝ → ℝ → ℝ) (V θ : ℝ → ℝ)
    {lo hi x : ℝ} (hx : x ∈ Ico lo hi)
    (hθ : ContinuousWithinAt θ (Ico lo hi) x)
    (hθnonnegative : ∀ y ∈ Ico lo hi, 0 ≤ θ y)
    (hvalue : ∀ y ∈ Ico lo hi, V y=F (θ y) y)
    (hmax : ∀ y ∈ Ico lo hi, ∀ u : ℝ, 0 ≤ u → F u y ≤ V y)
    (hder : ∀ y ∈ Ico lo hi, ∀ u : ℝ, 0 ≤ u →
      HasDerivAt (F u) (D u y) y)
    (hD : ContinuousAt (fun p : ℝ × ℝ => D p.1 p.2) (θ x,x)) :
    HasDerivWithinAt V (D (θ x) x) (Ico lo hi) x := by
  apply hasDerivWithinAt_iff_tendsto_slope.mpr
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ,hδ,hnear⟩ := Metric.continuousAt_iff.mp hD (ε/2) (half_pos hε)
  have hid : Tendsto (fun y : ℝ => y) (𝓝[Ico lo hi \ {x}] x) (𝓝 x) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hθ' : Tendsto θ (𝓝[Ico lo hi \ {x}] x) (𝓝 (θ x)) :=
    hθ.mono_left (nhdsWithin_mono x sdiff_subset)
  have hdx : Tendsto (fun y : ℝ => |y-x|)
      (𝓝[Ico lo hi \ {x}] x) (𝓝 0) := by
    simpa only [sub_self,abs_zero] using (hid.sub_const x).abs
  have hdθ : Tendsto (fun y : ℝ => |θ y-θ x|)
      (𝓝[Ico lo hi \ {x}] x) (𝓝 0) := by
    simpa only [sub_self,abs_zero] using (hθ'.sub_const (θ x)).abs
  filter_upwards [hdx.eventually_lt_const hδ,hdθ.eventually_lt_const hδ,
    self_mem_nhdsWithin] with y hxy hθy hy
  have hyI : y ∈ Ico lo hi := hy.1
  have hyne : y ≠ x := by simpa only [mem_singleton_iff] using hy.2
  have hsmall (u z : ℝ) (hu : u=θ x ∨ u=θ y) (hz : |z-x| < δ) :
      |D u z-D (θ x) x| ≤ ε/2 := by
    have hu' : |u-θ x| < δ := by
      rcases hu with rfl | rfl
      · simpa only [sub_self,abs_zero] using hδ
      · exact hθy
    have hdist : dist (u,z) (θ x,x) < δ := by
      rw [Prod.dist_eq,Real.dist_eq,Real.dist_eq]
      exact max_lt hu' hz
    have hh := hnear hdist
    simpa only [Real.dist_eq] using hh.le
  have hθ0 := hθnonnegative x hx
  have hθ1 := hθnonnegative y hyI
  have hslope : |(V y-V x)/(y-x)-D (θ x) x| ≤ ε/2 := by
    rcases lt_or_gt_of_ne hyne with hyx | hxy'
    · have hzI (z : ℝ) (hz : z ∈ Icc y x) : z ∈ Ico lo hi :=
        ⟨hyI.1.trans hz.1,hz.2.trans_lt hx.2⟩
      have hsz (z : ℝ) (hz : z ∈ Icc y x) : |z-x| < δ := by
        rw [abs_of_nonpos (sub_nonpos.mpr hz.2),neg_sub]
        have h := abs_lt.mp hxy
        linarith [hz.1,h.1]
      have hh := ordered_slope_bound F D V hyx
        (hvalue y hyI) (hvalue x hx)
        (hmax y hyI (θ x) hθ0) (hmax x hx (θ y) hθ1)
        (fun u hu z hz => hder z (hzI z hz) u (by
          rcases hu with rfl | rfl <;> assumption))
        (fun u hu z hz => hsmall u z (hu.symm) (hsz z hz))
      have he : (V x-V y)/(x-y)=(V y-V x)/(y-x) := by
        rw [← neg_sub x y,← neg_sub (V x) (V y),neg_div_neg_eq]
      rwa [he] at hh
    · have hzI (z : ℝ) (hz : z ∈ Icc x y) : z ∈ Ico lo hi :=
        ⟨hx.1.trans hz.1,hz.2.trans_lt hyI.2⟩
      have hsz (z : ℝ) (hz : z ∈ Icc x y) : |z-x| < δ := by
        rw [abs_of_nonneg (sub_nonneg.mpr hz.1)]
        have h := abs_lt.mp hxy
        linarith [hz.2,h.2]
      exact ordered_slope_bound F D V hxy'
        (hvalue x hx) (hvalue y hyI)
        (hmax x hx (θ y) hθ1) (hmax y hyI (θ x) hθ0)
        (fun u hu z hz => hder z (hzI z hz) u (by
          rcases hu with rfl | rfl <;> assumption))
        (fun u hu z hz => hsmall u z hu (hsz z hz))
  rw [Real.dist_eq,slope_fun_def_field]
  exact hslope.trans_lt (half_lt_self hε)

end FCAppendix.Affine.Uniform06.SelectedMaximumDerivative
