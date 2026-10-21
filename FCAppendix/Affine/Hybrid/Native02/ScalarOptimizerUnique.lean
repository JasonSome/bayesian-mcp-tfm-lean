import FCAppendix.Affine.Hybrid.Native02.SourceInterior

noncomputable section
namespace FCAppendix.Affine.Hybrid.Native02
open Set Filter Topology

private theorem phi_eq_ratio_of_interior_maximizer {xi z v lam q : ℝ}
    (hxi : 0 < xi) (hxi1 : xi < 1) (hz : 0 ≤ z) (hz1 : z < 1)
    (hv : 0 < v) (hq : q ∈ Ioo (0:ℝ) 1)
    (hmax : ∀ r ∈ Icc (0:ℝ) 1, two xi z v lam r ≤ two xi z v lam q) :
    phi xi z q = lam/v := by
  have hd : 0 < 1-xi*q := by nlinarith [hq.2]
  have he : 0 < 1-z := sub_pos.mpr hz1
  have hD : 0 < 1+z*xi/(2*(1-z)*(1-xi*q)^2) := by positivity
  have hm : IsLocalMax (two xi z v lam) q := by
    change ∀ᶠ r in nhds q, two xi z v lam r ≤ two xi z v lam q
    filter_upwards [Ioo_mem_nhds hq.1 hq.2] with r hr
    exact hmax r ⟨hr.1.le, hr.2.le⟩
  have hzero := hm.hasDerivAt_eq_zero (hasDerivAt_twoQ hd.ne')
  have hf := twoQDerivative_factor (xi := xi) (z := z) (v := v) (lam := lam) (q := q)
    hv.ne' he.ne' hd.ne' hD.ne'
  rw [hzero] at hf
  have hpos := twoQDerivative_factor_pos hxi hxi1 hz hz1 hv ⟨hq.1.le,hq.2.le⟩
  exact sub_eq_zero.mp ((mul_eq_zero.mp hf.symm).resolve_left hpos.ne')

theorem unitArgmax_two_eq_of_interior_maximizer {xi z v lam q : ℝ}
    (hxi : 0 < xi) (hxi1 : xi < 1) (hz : 0 ≤ z) (hz1 : z < 1)
    (hv : 0 < v) (hlam : 0 < lam) (hq : q ∈ Ioo (0:ℝ) 1)
    (hmax : ∀ r ∈ Icc (0:ℝ) 1, two xi z v lam r ≤ two xi z v lam q) :
    unitArgmax (two xi z v lam) (continuousOn_two_unit hxi hxi1 z v lam) = q := by
  have hphi := phi_eq_ratio_of_interior_maximizer hxi hxi1 hz hz1 hv hq hmax
  have hthreshold : lam/v < phi xi z 0 := by
    rw [←hphi]
    exact phi_strictAntiOn hxi hxi1 hz hz1 ⟨le_rfl,by norm_num⟩ ⟨hq.1.le,hq.2.le⟩ hq.1
  have hstar := unitArgmax_interior_of_phi_threshold hxi hxi1 hz hz1 hv hlam hthreshold
  have hmaxstar := (unitArgmax_spec (two xi z v lam) (continuousOn_two_unit hxi hxi1 z v lam)).2
  have hphistar := phi_eq_ratio_of_interior_maximizer hxi hxi1 hz hz1 hv hstar hmaxstar
  exact phi_injectiveOn hxi hxi1 hz hz1 ⟨hstar.1.le,hstar.2.le⟩ ⟨hq.1.le,hq.2.le⟩
    (hphistar.trans hphi.symm)

end FCAppendix.Affine.Hybrid.Native02
