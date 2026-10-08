import FCAppendix.Exclusive.NarrowCalculus
import FCAppendix.Exclusive.NarrowOrderedGraph
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace FCAppendix.Exclusive.Narrow
open MeasureTheory Filter Topology Set
open scoped BigOperators ContDiff

noncomputable def dfUnique (d : ℕ) (p : ℝ) : ℝ :=
  (d : ℝ) / (1 - p) ^ (d + 1)

noncomputable def dfOnce (d : ℕ) (p : ℝ) : ℝ :=
  (d : ℝ) * ((2 * d + 1 : ℕ) + (1 - p) ^ (d + 1)) /
    (((d + 1 : ℕ) : ℝ) * (1 - p) ^ (2 * d + 2))

noncomputable def dfPerInclusion (d : ℕ) (p : ℝ) : ℝ :=
  (d : ℝ) * (((2 * d + 1 : ℕ) : ℝ) - 2 * ((d : ℝ) - 1) * (1 - p)) /
    (1 - p) ^ (2 * d + 2)

noncomputable def dfTariff (d : ℕ) (a : UserTariff) (p : ℝ) : ℝ :=
  match a with
  | .unique => dfUnique d p
  | .affine eta => (1 - eta) * dfOnce d p + eta * dfPerInclusion d p

theorem fOnce_split (d : ℕ) (hd : 1 ≤ d) (p : ℝ) :
    fOnce d p = ((d : ℝ) / ((d + 1 : ℕ) : ℝ)) * fUnique (2 * d + 1) p +
      (1 / ((d + 1 : ℕ) : ℝ)) * fUnique d p := by
  by_cases hp : p = 1
  · subst p
    simp [fOnce, fUnique, show d ≠ 0 by omega]
  · have hq : 1 - p ≠ 0 := sub_ne_zero.mpr (Ne.symm hp)
    have hn : ((d + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    have he : (1 - p) ^ (2 * d + 1) = (1 - p) ^ (d + 1) * (1 - p) ^ d := by
      rw [← pow_add]
      congr 1; omega
    unfold fOnce fUnique
    rw [he]
    field_simp [hn, hq, pow_ne_zero d hq, pow_ne_zero (d + 1) hq]

theorem fPerInclusion_split (d : ℕ) (hd : 1 ≤ d) (p : ℝ) :
    fPerInclusion d p = (d : ℝ) * fUnique (2 * d + 1) p -
      ((d : ℝ) - 1) * fUnique (2 * d) p := by
  by_cases hp : p = 1
  · subst p
    simp [fPerInclusion, fUnique, show 2 * d ≠ 0 by omega]
  · have hq : 1 - p ≠ 0 := sub_ne_zero.mpr (Ne.symm hp)
    unfold fPerInclusion fUnique
    rw [pow_succ]
    field_simp [hq, pow_ne_zero (2 * d) hq]

theorem hasDerivAt_fUnique (d : ℕ) (hd : 1 ≤ d) (p : ℝ) (hp : p < 1) :
    HasDerivAt (fUnique d) (dfUnique d p) p := by
  change HasDerivAt (referenceBid d 1) (dfUnique d p) p
  simpa only [dfUnique, one_mul] using
    hasDerivAt_referenceBid d hd 1 p hp

theorem hasDerivAt_fOnce (d : ℕ) (hd : 1 ≤ d) (p : ℝ) (hp : p < 1) :
    HasDerivAt (fOnce d) (dfOnce d p) p := by
  have hq : 1 - p ≠ 0 := (sub_pos.mpr hp).ne'
  have hn : ((d + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have he : fOnce d = fun x => ((d : ℝ) / ((d + 1 : ℕ) : ℝ)) * fUnique (2 * d + 1) x +
      (1 / ((d + 1 : ℕ) : ℝ)) * fUnique d x := funext (fOnce_split d hd)
  rw [he]
  convert ((hasDerivAt_fUnique (2 * d + 1) (by omega) p hp).const_mul
    ((d : ℝ) / ((d + 1 : ℕ) : ℝ))).add
      ((hasDerivAt_fUnique d hd p hp).const_mul (1 / ((d + 1 : ℕ) : ℝ))) using 1 <;> try rfl
  have hpow : (1 - p) ^ (2 * d + 2) = ((1 - p) ^ (d + 1)) ^ 2 := by
    rw [← pow_mul]
    congr 1; omega
  simp only [dfUnique, dfOnce, show 2 * d + 1 + 1 = 2 * d + 2 by omega,
    hpow, Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat]
  field_simp [hn, hq, pow_ne_zero (d + 1) hq]

theorem hasDerivAt_fPerInclusion (d : ℕ) (hd : 1 ≤ d) (p : ℝ) (hp : p < 1) :
    HasDerivAt (fPerInclusion d) (dfPerInclusion d p) p := by
  have hq : 1 - p ≠ 0 := (sub_pos.mpr hp).ne'
  have he : fPerInclusion d = fun x => (d : ℝ) * fUnique (2 * d + 1) x -
      ((d : ℝ) - 1) * fUnique (2 * d) x := funext (fPerInclusion_split d hd)
  rw [he]
  convert ((hasDerivAt_fUnique (2 * d + 1) (by omega) p hp).const_mul (d : ℝ)).sub
    ((hasDerivAt_fUnique (2 * d) (by omega) p hp).const_mul ((d : ℝ) - 1)) using 1 <;> try rfl
  have hpow : (1 - p) ^ (2 * d + 2) = (1 - p) ^ (2 * d + 1) * (1 - p) := by
    rw [← pow_succ]
  simp only [dfUnique, dfPerInclusion,
    show 2 * d + 1 + 1 = 2 * d + 2 by omega, hpow,
    Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat]
  field_simp [hq, pow_ne_zero (2 * d + 1) hq]

theorem hasDerivAt_fTariff (d : ℕ) (hd : 1 ≤ d) (a : UserTariff)
    (p : ℝ) (hp : p < 1) : HasDerivAt (fTariff d a) (dfTariff d a p) p := by
  cases a with
  | unique => exact hasDerivAt_fUnique d hd p hp
  | affine eta =>
    exact ((hasDerivAt_fOnce d hd p hp).const_mul (1 - eta)).add
      ((hasDerivAt_fPerInclusion d hd p hp).const_mul eta)

theorem fUnique_pos (d : ℕ) {p : ℝ} (hp : p < 1) : 0 < fUnique d p :=
  div_pos zero_lt_one (pow_pos (sub_pos.mpr hp) d)

theorem fOnce_pos (d : ℕ) (hd : 1 ≤ d) {p : ℝ} (hp : p < 1) : 0 < fOnce d p := by
  unfold fOnce
  have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr (by omega)
  exact div_pos (add_pos hdR (pow_pos (sub_pos.mpr hp) _))
    (mul_pos (by positivity) (pow_pos (sub_pos.mpr hp) _))

theorem fPerInclusion_pos (d : ℕ) (hd : 1 ≤ d) {p : ℝ}
    (hp0 : 0 ≤ p) (hp : p < 1) : 0 < fPerInclusion d p := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hn : 0 < (d : ℝ) - ((d : ℝ) - 1) * (1 - p) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hdR) hp0]
  exact div_pos hn (pow_pos (sub_pos.mpr hp) _)

theorem dfUnique_pos (d : ℕ) (hd : 1 ≤ d) {p : ℝ} (hp : p < 1) : 0 < dfUnique d p :=
  div_pos (by exact_mod_cast (show 0 < d by omega)) (pow_pos (sub_pos.mpr hp) _)

theorem dfOnce_pos (d : ℕ) (hd : 1 ≤ d) {p : ℝ} (hp : p < 1) : 0 < dfOnce d p := by
  unfold dfOnce
  exact div_pos (mul_pos (by exact_mod_cast (show 0 < d by omega))
    (add_pos (by positivity) (pow_pos (sub_pos.mpr hp) _)))
    (mul_pos (by positivity) (pow_pos (sub_pos.mpr hp) _))

theorem dfPerInclusion_pos (d : ℕ) (hd : 1 ≤ d) {p : ℝ}
    (hp0 : 0 ≤ p) (hp : p < 1) : 0 < dfPerInclusion d p := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hnum : 0 < (((2 * d + 1 : ℕ) : ℝ) - 2 * ((d : ℝ) - 1) * (1 - p)) := by
    push_cast
    nlinarith [mul_nonneg (sub_nonneg.mpr hdR) hp0]
  exact div_pos (mul_pos (by exact_mod_cast (show 0 < d by omega)) hnum)
    (pow_pos (sub_pos.mpr hp) _)

private theorem mixture_mem_Icc {eta L U x y : ℝ} (h0 : 0 ≤ eta) (h1 : eta ≤ 1)
    (hx : x ∈ Icc L U) (hy : y ∈ Icc L U) :
    (1 - eta) * x + eta * y ∈ Icc L U := by
  constructor
  · have h := add_le_add (mul_le_mul_of_nonneg_left hx.1 (sub_nonneg.mpr h1))
      (mul_le_mul_of_nonneg_left hy.1 h0)
    nlinarith
  · have h := add_le_add (mul_le_mul_of_nonneg_left hx.2 (sub_nonneg.mpr h1))
      (mul_le_mul_of_nonneg_left hy.2 h0)
    nlinarith

theorem fTariff_pos_and_derivative_pos (d : ℕ) (hd : 1 ≤ d)
    (a : UserTariff) (ha : a.Allowed) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1) :
    0 < fTariff d a p ∧ 0 < dfTariff d a p := by
  cases a with
  | unique => exact ⟨fUnique_pos d hp1, dfUnique_pos d hd hp1⟩
  | affine eta =>
    have hcomb {x y : ℝ} (hx : 0 < x) (hy : 0 < y) : 0 < (1 - eta) * x + eta * y := by
      by_cases he : eta = 1
      · simp [he, hy]
      · exact add_pos_of_pos_of_nonneg
          (mul_pos (sub_pos.mpr (lt_of_le_of_ne ha.2 he)) hx) (mul_nonneg ha.1 hy.le)
    exact ⟨hcomb (fOnce_pos d hd hp1) (fPerInclusion_pos d hd hp0 hp1),
      hcomb (dfOnce_pos d hd hp1) (dfPerInclusion_pos d hd hp0 hp1)⟩

private theorem continuousOn_df_endpoints (d : ℕ) :
    ContinuousOn (dfUnique d) (Iio 1) ∧
      ContinuousOn (dfOnce d) (Iio 1) ∧ ContinuousOn (dfPerInclusion d) (Iio 1) := by
  have hq (p : ℝ) (hp : p ∈ Iio (1 : ℝ)) : 0 < 1 - p := sub_pos.mpr hp
  constructor
  · intro p hp
    have hqp := hq p hp
    apply ContinuousAt.continuousWithinAt
    unfold dfUnique
    fun_prop (disch := positivity)
  constructor
  · intro p hp
    have hqp := hq p hp
    apply ContinuousAt.continuousWithinAt
    unfold dfOnce
    fun_prop (disch := positivity)
  · intro p hp
    have hqp := hq p hp
    apply ContinuousAt.continuousWithinAt
    unfold dfPerInclusion
    fun_prop (disch := positivity)

private theorem positive_compact_bounds {J : Set ℝ} (hJ : IsCompact J)
    (hne : J.Nonempty) {f : ℝ → ℝ} (hf : ContinuousOn f J)
    (hpos : ∀ p ∈ J, 0 < f p) :
    ∃ L U : ℝ, 0 < L ∧ L ≤ U ∧ ∀ p ∈ J, f p ∈ Icc L U := by
  obtain ⟨p, hp, hmin⟩ := hJ.exists_isMinOn hne hf
  obtain ⟨q, hq, hmax⟩ := hJ.exists_isMaxOn hne hf
  rw [isMinOn_iff] at hmin
  rw [isMaxOn_iff] at hmax
  exact ⟨f p, f q, hpos p hp, hmax p hp, fun x hx => ⟨hmin x hx, hmax x hx⟩⟩

theorem source_tariff_uniform_bounds (d : ℕ) (hd : 1 ≤ d)
    {l u : ℝ} (hl : 0 ≤ l) (hlu : l ≤ u) (hu : u < 1) :
    ∃ Fmin Fmax Dmin Dmax : ℝ,
      0 < Fmin ∧ Fmin ≤ Fmax ∧ 0 < Dmin ∧ Dmin ≤ Dmax ∧
      ∀ a : UserTariff, a.Allowed → ∀ p ∈ Icc l u,
        fTariff d a p ∈ Icc Fmin Fmax ∧ dfTariff d a p ∈ Icc Dmin Dmax := by
  let J := Icc l u
  have hJ : J ⊆ Iio (1 : ℝ) := fun p hp => lt_of_le_of_lt hp.2 hu
  have hne : J.Nonempty := ⟨l, left_mem_Icc.mpr hlu⟩
  have hfu : ContinuousOn (fUnique d) J := fun p hp =>
    (hasDerivAt_fUnique d hd p (hJ hp)).continuousAt.continuousWithinAt
  have hf0 : ContinuousOn (fOnce d) J := fun p hp =>
    (hasDerivAt_fOnce d hd p (hJ hp)).continuousAt.continuousWithinAt
  have hf1 : ContinuousOn (fPerInclusion d) J := fun p hp =>
    (hasDerivAt_fPerInclusion d hd p (hJ hp)).continuousAt.continuousWithinAt
  obtain ⟨Lu, Uu, hLu, _, hbu⟩ := positive_compact_bounds isCompact_Icc hne hfu
    (fun p hp => fUnique_pos d (hJ hp))
  obtain ⟨L0, U0, hL0, _, hb0⟩ := positive_compact_bounds isCompact_Icc hne hf0
    (fun p hp => fOnce_pos d hd (hJ hp))
  obtain ⟨L1, U1, hL1, _, hb1⟩ := positive_compact_bounds isCompact_Icc hne hf1
    (fun p hp => fPerInclusion_pos d hd (hl.trans hp.1) (hJ hp))
  have hdcont := continuousOn_df_endpoints d
  obtain ⟨lu, uu, hlu0, _, hdu⟩ := positive_compact_bounds isCompact_Icc hne
    (hdcont.1.mono hJ) (fun p hp => dfUnique_pos d hd (hJ hp))
  obtain ⟨l0, u0, hl00, _, hd0⟩ := positive_compact_bounds isCompact_Icc hne
    (hdcont.2.1.mono hJ) (fun p hp => dfOnce_pos d hd (hJ hp))
  obtain ⟨l1, u1, hl10, _, hd1⟩ := positive_compact_bounds isCompact_Icc hne
    (hdcont.2.2.mono hJ) (fun p hp => dfPerInclusion_pos d hd (hl.trans hp.1) (hJ hp))
  let Fmin := min Lu (min L0 L1)
  let Fmax := max Uu (max U0 U1)
  let Dmin := min lu (min l0 l1)
  let Dmax := max uu (max u0 u1)
  have hFmin : 0 < Fmin := lt_min hLu (lt_min hL0 hL1)
  have hDmin : 0 < Dmin := lt_min hlu0 (lt_min hl00 hl10)
  have hfbu (p : ℝ) (hp : p ∈ J) : fUnique d p ∈ Icc Fmin Fmax :=
    ⟨(min_le_left _ _).trans (hbu p hp).1, (hbu p hp).2.trans (le_max_left _ _)⟩
  have hfb0 (p : ℝ) (hp : p ∈ J) : fOnce d p ∈ Icc Fmin Fmax :=
    ⟨((min_le_right _ _).trans (min_le_left _ _)).trans (hb0 p hp).1,
      (hb0 p hp).2.trans ((le_max_left _ _).trans (le_max_right _ _))⟩
  have hfb1 (p : ℝ) (hp : p ∈ J) : fPerInclusion d p ∈ Icc Fmin Fmax :=
    ⟨((min_le_right _ _).trans (min_le_right _ _)).trans (hb1 p hp).1,
      (hb1 p hp).2.trans ((le_max_right _ _).trans (le_max_right _ _))⟩
  have hdbu (p : ℝ) (hp : p ∈ J) : dfUnique d p ∈ Icc Dmin Dmax :=
    ⟨(min_le_left _ _).trans (hdu p hp).1, (hdu p hp).2.trans (le_max_left _ _)⟩
  have hdb0 (p : ℝ) (hp : p ∈ J) : dfOnce d p ∈ Icc Dmin Dmax :=
    ⟨((min_le_right _ _).trans (min_le_left _ _)).trans (hd0 p hp).1,
      (hd0 p hp).2.trans ((le_max_left _ _).trans (le_max_right _ _))⟩
  have hdb1 (p : ℝ) (hp : p ∈ J) : dfPerInclusion d p ∈ Icc Dmin Dmax :=
    ⟨((min_le_right _ _).trans (min_le_right _ _)).trans (hd1 p hp).1,
      (hd1 p hp).2.trans ((le_max_right _ _).trans (le_max_right _ _))⟩
  refine ⟨Fmin, Fmax, Dmin, Dmax, hFmin,
    (hfbu l (left_mem_Icc.mpr hlu)).1.trans (hfbu l (left_mem_Icc.mpr hlu)).2,
    hDmin, (hdbu l (left_mem_Icc.mpr hlu)).1.trans (hdbu l (left_mem_Icc.mpr hlu)).2, ?_⟩
  intro a ha p hp
  cases a with
  | unique => exact ⟨hfbu p hp, hdbu p hp⟩
  | affine eta =>
    exact ⟨mixture_mem_Icc ha.1 ha.2 (hfb0 p hp) (hfb1 p hp),
      mixture_mem_Icc ha.1 ha.2 (hdb0 p hp) (hdb1 p hp)⟩

theorem contDiff_binomialPolynomial (n : ℕ) (f : ℕ → ℝ) :
    ContDiff ℝ ∞ (binomialPolynomial n f) := by
  induction n generalizing f with
  | zero => exact contDiff_const
  | succ n ih =>
    exact ((contDiff_const.sub contDiff_id).mul (ih f)).add
      (contDiff_id.mul (ih (fun r => f (1 + r))))

theorem contDiff_binomialPolynomialDerivative (n : ℕ) (f : ℕ → ℝ) :
    ContDiff ℝ ∞ (binomialPolynomialDerivative n f) := by
  induction n generalizing f with
  | zero => exact contDiff_const
  | succ n ih =>
    exact ((((contDiff_binomialPolynomial n f).neg.add
      ((contDiff_const.sub contDiff_id).mul (ih f))).add
      (contDiff_binomialPolynomial n (fun r => f (1 + r)))).add
      (contDiff_id.mul (ih (fun r => f (1 + r)))))

theorem contDiffOn_baseMarginalCost (d : ℕ) (G : Schedule (d + 1)) :
    ContDiffOn ℝ ∞ (baseMarginalCost d G) (Iio 1) := by
  apply (contDiff_binomialPolynomialDerivative (d + 1) G.charge).contDiffOn.div
    (contDiff_const.mul ((contDiff_const.sub contDiff_id).pow d)).contDiffOn
  intro p hp
  exact mul_ne_zero (by positivity) (pow_ne_zero _ (sub_pos.mpr hp).ne')

theorem hasDerivAt_baseMarginalCost (d : ℕ) (G : Schedule (d + 1))
    (p : ℝ) (hp : p < 1) :
    HasDerivAt (baseMarginalCost d G) (deriv (baseMarginalCost d G) p) p := by
  exact (((contDiffOn_baseMarginalCost d G).differentiableOn (by simp)) p hp).differentiableAt
    (isOpen_Iio.mem_nhds hp) |>.hasDerivAt

theorem base_derivative_bound (d : ℕ) (G : Schedule (d + 1))
    {l u : ℝ} (hlu : l ≤ u) (hu : u < 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ p ∈ Icc l u, |deriv (baseMarginalCost d G) p| ≤ K := by
  have hcont : ContinuousOn (fun p => |deriv (baseMarginalCost d G) p|) (Icc l u) :=
    ((contDiffOn_baseMarginalCost d G).continuousOn_deriv_of_isOpen isOpen_Iio (by simp)).abs.mono
      (fun p hp => lt_of_le_of_lt hp.2 hu)
  obtain ⟨p, hp, hmax⟩ := isCompact_Icc.exists_isMaxOn
    ⟨l, left_mem_Icc.mpr hlu⟩ hcont
  rw [isMaxOn_iff] at hmax
  exact ⟨_, abs_nonneg _, hmax⟩

noncomputable def exposureEquation (d : ℕ) (a : UserTariff) (G : Schedule (d + 1))
    (g lam p : ℝ) : ℝ := lam * fTariff d a p + g * baseMarginalCost d G p

theorem hasDerivAt_exposureEquation (d : ℕ) (hd : 1 ≤ d) (a : UserTariff)
    (G : Schedule (d + 1)) (g lam p : ℝ) (hp : p < 1) :
    HasDerivAt (exposureEquation d a G g lam)
      (lam * dfTariff d a p + g * deriv (baseMarginalCost d G) p) p :=
  ((hasDerivAt_fTariff d hd a p hp).const_mul lam).add
    ((hasDerivAt_baseMarginalCost d G p hp).const_mul g)

theorem exists_uniform_small_base_guard (d : ℕ) (hd : 1 ≤ d)
    (G : Schedule (d + 1)) {l u L U : ℝ}
    (hl : 0 ≤ l) (hlu : l ≤ u) (hu : u < 1) (hL : 0 < L) (_hLU : L ≤ U) :
    ∃ eps Fmin Fmax Dmin Dmax K : ℝ,
      0 < eps ∧ 0 < Fmin ∧ Fmin ≤ Fmax ∧ 0 < Dmin ∧ Dmin ≤ Dmax ∧ 0 ≤ K ∧
      (∀ a : UserTariff, a.Allowed → ∀ p ∈ Icc l u,
        fTariff d a p ∈ Icc Fmin Fmax ∧ dfTariff d a p ∈ Icc Dmin Dmax) ∧
      ∀ H g lam : ℝ, 0 < H → 0 ≤ g → g / H < eps →
        lam ∈ Icc (H * L) (H * U) → ∀ a : UserTariff, a.Allowed →
        (∀ p ∈ Icc l u,
          H * L * Dmin / 2 ≤ lam * dfTariff d a p + g * deriv (baseMarginalCost d G) p) ∧
        StrictMonoOn (exposureEquation d a G g lam) (Icc l u) := by
  obtain ⟨Fmin, Fmax, Dmin, Dmax, hFm, hFM, hDm, hDM, hbounds⟩ :=
    source_tariff_uniform_bounds d hd hl hlu hu
  obtain ⟨K, hK, hKb⟩ := base_derivative_bound d G hlu hu
  let eps := L * Dmin / (2 * (K + 1))
  have heps : 0 < eps := div_pos (mul_pos hL hDm) (by positivity)
  refine ⟨eps, Fmin, Fmax, Dmin, Dmax, K, heps, hFm, hFM, hDm, hDM, hK, hbounds, ?_⟩
  intro H g lam hH hg hsmall hlam a ha
  have hsg : g * K < H * L * Dmin / 2 := by
    have hs : g < eps * H := (div_lt_iff₀ hH).mp hsmall
    have hden : 0 < 2 * (K + 1) := by positivity
    have he : eps * (2 * (K + 1)) = L * Dmin := by
      dsimp [eps]
      exact div_mul_cancel₀ _ hden.ne'
    have hmul := mul_lt_mul_of_pos_right hs hden
    have heH : eps * H * (2 * (K + 1)) = H * L * Dmin := by
      calc
        _ = H * (eps * (2 * (K + 1))) := by ring
        _ = H * (L * Dmin) := by rw [he]
        _ = _ := by ring
    rw [heH] at hmul
    nlinarith
  have hlow : ∀ p ∈ Icc l u,
      H * L * Dmin / 2 ≤ lam * dfTariff d a p + g * deriv (baseMarginalCost d G) p := by
    intro p hp
    have hlamp : 0 < lam := (mul_pos hH hL).trans_le hlam.1
    have hdf := (hbounds a ha p hp).2.1
    have hprod : H * L * Dmin ≤ lam * dfTariff d a p :=
      mul_le_mul hlam.1 hdf hDm.le hlamp.le
    have hb := (abs_le.mp (hKb p hp)).1
    have hgder := mul_le_mul_of_nonneg_left hb hg
    nlinarith
  refine ⟨hlow, ?_⟩
  apply strictMonoOn_of_deriv_pos (convex_Icc l u)
    (fun p hp => (hasDerivAt_exposureEquation d hd a G g lam p
      (lt_of_le_of_lt hp.2 hu)).continuousAt.continuousWithinAt)
  intro p hp
  have hpJ : p ∈ Icc l u := interior_subset hp
  rw [(hasDerivAt_exposureEquation d hd a G g lam p (lt_of_le_of_lt hpJ.2 hu)).deriv]
  exact (by positivity : 0 < H * L * Dmin / 2).trans_le (hlow p hpJ)

structure LocalExposureSolution (μ : Measure ℝ) (J : Set ℝ)
    (f hbase : ℝ → ℝ) (g rho lam : ℝ) (p : ℝ → ℝ) : Prop where
  integrable : Integrable p μ
  mem : ∀ᵐ v ∂μ, p v ∈ J
  equation : ∀ᵐ v ∂μ, v = lam * f (p v) + g * hbase (p v)
  capacity : ∫ v, p v ∂μ = rho

theorem local_exposure_strict_price_order {J : Set ℝ} {f hbase : ℝ → ℝ}
    {g lam tau v p q : ℝ} (hlt : lam < tau) (hp : p ∈ J) (hq : q ∈ J)
    (hf : ∀ x ∈ J, 0 < f x)
    (hmono : StrictMonoOn (fun x => lam * f x + g * hbase x) J)
    (heq : v = lam * f p + g * hbase p)
    (heq' : v = tau * f q + g * hbase q) : q < p := by
  have hprice : lam * f q + g * hbase q < tau * f q + g * hbase q := by
    nlinarith [mul_pos (sub_pos.mpr hlt) (hf q hq)]
  by_contra hn
  have hpq : p ≤ q := le_of_not_gt hn
  have hle := hmono.monotoneOn hp hq hpq
  linarith

theorem local_capacity_uniqueness {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hμ : μ ≠ 0) {J Lset : Set ℝ} {f hbase : ℝ → ℝ} {g rho lam tau : ℝ}
    {p q : ℝ → ℝ} (hlam : lam ∈ Lset) (htau : tau ∈ Lset)
    (hf : ∀ x ∈ J, 0 < f x)
    (hmono : ∀ s ∈ Lset, StrictMonoOn (fun x => s * f x + g * hbase x) J)
    (hp : LocalExposureSolution μ J f hbase g rho lam p)
    (hq : LocalExposureSolution μ J f hbase g rho tau q) :
    lam = tau ∧ p =ᵐ[μ] q := by
  have hno {s t : ℝ} {x y : ℝ → ℝ} (hst : s < t) (hs : s ∈ Lset)
      (hx : LocalExposureSolution μ J f hbase g rho s x)
      (hy : LocalExposureSolution μ J f hbase g rho t y) : False := by
    have hstrict : ∀ᵐ v ∂μ, y v < x v := by
      filter_upwards [hx.mem, hy.mem, hx.equation, hy.equation] with v hvx hvy hex hey
      exact local_exposure_strict_price_order hst hvx hvy hf (hmono s hs) hex hey
    have hle : y ≤ᵐ[μ] x := hstrict.mono (fun _ h => h.le)
    have heq : y =ᵐ[μ] x :=
      (integral_eq_iff_of_ae_le hy.integrable hx.integrable hle).mp
        (hy.capacity.trans hx.capacity.symm)
    letI : NeZero μ := ⟨hμ⟩
    obtain ⟨v, hvlt, hveq⟩ := (hstrict.and heq).exists
    exact (ne_of_lt hvlt) hveq
  have he : lam = tau := by
    rcases lt_trichotomy lam tau with h | h | h
    · exact False.elim (hno h hlam hp hq)
    · exact h
    · exact False.elim (hno h htau hq hp)
  refine ⟨he, ?_⟩
  filter_upwards [hp.mem, hq.mem, hp.equation, hq.equation] with v hvp hvq hep heq
  apply (hmono lam hlam).injOn hvp hvq
  dsimp only
  rw [← hep, he, ← heq]

end FCAppendix.Exclusive.Narrow
