import FCAppendix.PayOnce.KernelDerivative

namespace FCAppendix.PayOnce.OwnImpact

open Filter Topology Set Finset CommonList
open scoped BigOperators

theorem focal_kernel_eq_of_roots {ι : Type*} [Fintype ι]
    {n : ℕ} (hn : 2 ≤ n) (b : ℝ) (rivals : ι → ℝ) {L T c : ℝ}
    (hL : 0 < L) (hT : 0 < T)
    (hcapL : kernel n b L + ∑ j, kernel n (rivals j) L = c)
    (hcapT : kernel n b T + ∑ j, kernel n (rivals j) T = c) :
    kernel n b L = kernel n b T := by
  have hdir {L T : ℝ} (hL : 0 < L) (hT : 0 < T) (hLT : L ≤ T)
      (hl : kernel n b L + ∑ j, kernel n (rivals j) L = c)
      (ht : kernel n b T + ∑ j, kernel n (rivals j) T = c) :
      kernel n b L = kernel n b T := by
    have hp := KernelTailEvent.kernel_antitone_price hn hL hT hLT (b := b)
    have hs := sum_le_sum (s := (univ : Finset ι))
      (fun j _ => KernelTailEvent.kernel_antitone_price hn hL hT hLT (b := rivals j))
    linarith
  rcases le_total L T with h | h
  · exact hdir hL hT h hcapL hcapT
  · exact (hdir hT hL h hcapT hcapL).symm

theorem exists_local_focal_branch {n : ℕ} (hn : 2 ≤ n)
    (R : ℝ → ℝ) {L b D : ℝ} (hL : 0 < L) (hb : 0 < b) (hD : 0 ≤ D)
    (hR : HasStrictDerivAt R D L) (hi : R L ∈ Ioo (0 : ℝ) 1)
    (hscore : b * H n (R L) = L) :
    ∃ T : ℝ → ℝ,
      HasStrictDerivAt (fun x => R (T x))
        (D * H n (R L) / (1 + b * Hslope n (R L) * D)) b ∧
      ∀ᶠ x in 𝓝 b, 0 < x ∧ 0 < T x ∧ R (T x) ∈ Ioo (0 : ℝ) 1 ∧
        kernel n x (T x) = R (T x) := by
  let F : ℝ → ℝ := fun z => z / H n (R z)
  let H0 := H n (R L)
  let D0 := Hslope n (R L)
  have hH : 0 < H0 := H_pos n (by omega) _ hi.1.le hi.2.le
  have hD0 : 0 < D0 := Hslope_pos hn ⟨hi.1.le, hi.2.le⟩
  have hF : HasStrictDerivAt F ((H0 + L * D0 * D) / H0 ^ 2) L := by
    have hh := (hasStrictDerivAt_H n (R L)).comp L hR
    have h := (hasStrictDerivAt_id L).div hh hH.ne'
    convert h using 1 <;> first | rfl | (dsimp only [H0, D0, Function.comp_def, id_eq]; ring)
  have hFpos : 0 < (H0 + L * D0 * D) / H0 ^ 2 := by
    apply div_pos _ (sq_pos_of_pos hH)
    exact add_pos_of_pos_of_nonneg hH (mul_nonneg (mul_pos hL hD0).le hD)
  have hFb : F L = b := by
    exact (div_eq_iff hH.ne').mpr hscore.symm
  let T := hF.localInverse F _ L hFpos.ne'
  have hTL : T (F L) = L :=
    HasStrictFDerivAt.localInverse_apply_image ..
  have hT := hF.to_localInverse hFpos.ne'
  change HasStrictDerivAt T (((H0 + L * D0 * D) / H0 ^ 2)⁻¹) (F L) at hT
  have hR' : HasStrictDerivAt R D (T (F L)) := by rw [hTL]; exact hR
  have hcomp := hR'.comp (F L) hT
  have hcomp' : HasStrictDerivAt (fun x => R (T x))
      (D * H n (R L) / (1 + b * Hslope n (R L) * D)) b := by
    rw [hFb] at hcomp
    convert hcomp using 1 <;> try rfl
    change D * H0 / (1 + b * D0 * D) = D * ((H0 + L * D0 * D) / H0 ^ 2)⁻¹
    have hsc : b * H0 = L := hscore
    have hz : 1 + b * D0 * D ≠ 0 := by positivity
    field_simp
    rw [← hsc]
    ring
  have hTcont : Tendsto T (𝓝 b) (𝓝 L) := by
    have hh := hT.hasDerivAt.continuousAt.tendsto
    rwa [hTL, hFb] at hh
  have hRcont : Tendsto (fun x => R (T x)) (𝓝 b) (𝓝 (R L)) :=
    hR.hasDerivAt.continuousAt.tendsto.comp hTcont
  have hinv := hF.eventually_right_inverse hFpos.ne'
  change ∀ᶠ x in 𝓝 (F L), F (T x) = x at hinv
  rw [hFb] at hinv
  refine ⟨T, hcomp', ?_⟩
  filter_upwards [eventually_gt_nhds hb, hTcont.eventually (Ioi_mem_nhds hL),
    hRcont.eventually (isOpen_Ioo.mem_nhds hi), hinv] with x hx htx hrx hfx
  refine ⟨hx, htx, hrx, ?_⟩
  have hHx := H_pos n (by omega) _ hrx.1.le hrx.2.le
  have hTx : T x = x * H n (R (T x)) := (div_eq_iff hHx.ne').mp hfx
  conv_lhs => rw [hTx]
  exact KernelTailEvent.kernel_at_score hn hx hrx.1.le hrx.2.le

noncomputable def rivalSensitivity {ι : Type*} [Fintype ι]
    (n : ℕ) (rivals : ι → ℝ) (L : ℝ) : ℝ :=
  ∑ j, if 0 < kernel n (rivals j) L ∧ kernel n (rivals j) L < 1
    then sensitivity n (rivals j) (kernel n (rivals j) L) else 0

theorem hasStrictDerivAt_focal_kernel {ι : Type*} [Fintype ι]
    {n : ℕ} (hn : 2 ≤ n) (rivals : ι → ℝ) (hr : ∀ j, 0 < rivals j)
    (f : ℝ → ℝ) {b L c : ℝ} (hb : 0 < b) (hL : 0 < L)
    (hcap : kernel n b L + ∑ j, kernel n (rivals j) L = c)
    (hi : kernel n b L ∈ Ioo (0 : ℝ) 1)
    (hclip0 : ∀ j, rivals j ≠ L) (hclip1 : ∀ j, rivals j ≠ (n : ℝ) * L)
    (hroot : ∀ x, 0 < x → ∃ T, 0 < T ∧ f x = kernel n x T ∧
      kernel n x T + ∑ j, kernel n (rivals j) T = c) :
    HasStrictDerivAt f
      (rivalSensitivity n rivals L * H n (kernel n b L) /
        (1 + b * Hslope n (kernel n b L) * rivalSensitivity n rivals L)) b := by
  classical
  let d : ι → ℝ := fun j => if 0 < kernel n (rivals j) L ∧ kernel n (rivals j) L < 1
    then sensitivity n (rivals j) (kernel n (rivals j) L) else 0
  let R : ℝ → ℝ := fun T => c - ∑ j, kernel n (rivals j) T
  have hterms (j : ι) : HasStrictDerivAt (kernel n (rivals j)) (-d j) L := by
    have hh := hasStrictDerivAt_kernel_price hn (hr j) hL (hclip0 j) (hclip1 j)
    convert hh using 1
    dsimp only [d]
    split_ifs <;> simp only [neg_zero]
  have hR : HasStrictDerivAt R (rivalSensitivity n rivals L) L := by
    have hh := (HasStrictDerivAt.fun_sum (fun j (_ : j ∈ (Finset.univ : Finset ι)) => hterms j)).const_sub c
    convert hh using 1 <;> try rfl
    simp only [rivalSensitivity, sum_neg_distrib, neg_neg, d]
  have hRL : R L = kernel n b L := by dsimp only [R]; linarith
  have hD : 0 ≤ rivalSensitivity n rivals L := by
    apply sum_nonneg
    intro j _
    split_ifs with hj
    · exact (sensitivity_pos hn (hr j) ⟨hj.1.le, hj.2.le⟩).le
    · exact le_rfl
  have hscore : b * H n (R L) = L := by
    rw [hRL]
    exact (scalarThreshold_kernel n hn hb hL).2.2.2.2 hi.1 hi.2
  obtain ⟨T, hT, he⟩ := exists_local_focal_branch hn R hL hb hD hR (by rwa [hRL]) hscore
  rw [hRL] at hT
  apply hT.congr_of_eventuallyEq
  filter_upwards [he] with x hx
  obtain ⟨U, hU, hf, hUcap⟩ := hroot x hx.1
  have hTcap : kernel n x (T x) + ∑ j, kernel n (rivals j) (T x) = c := by
    rw [hx.2.2.2]
    dsimp only [R]
    ring
  exact hx.2.2.2.symm.trans ((focal_kernel_eq_of_roots hn x rivals hx.2.1 hU hTcap hUcap).trans hf.symm)

noncomputable def focalWeight (n : ℕ) (b p D : ℝ) : ℝ :=
  sensitivity n b p / (sensitivity n b p + D)

theorem focal_derivative_weight_identity {n : ℕ} (hn : 2 ≤ n) {b p D : ℝ}
    (hb : 0 < b) (hp : p ∈ Icc (0 : ℝ) 1) (hD : 0 ≤ D) :
    D * H n p / (1 + b * Hslope n p * D) =
      H n p / (b * Hslope n p) * (1 - focalWeight n b p D) := by
  have hbd : 0 < b * Hslope n p := mul_pos hb (Hslope_pos hn hp)
  have hden : 0 < 1 + b * Hslope n p * D :=
    add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg hbd.le hD)
  have hs : 0 < sensitivity n b p + D := add_pos_of_pos_of_nonneg
    (sensitivity_pos hn hb hp) hD
  unfold focalWeight sensitivity
  dsimp only [sensitivity] at hs
  field_simp [hb.ne', (Hslope_pos hn hp).ne', hden.ne', hs.ne']
  have hsp := Hslope_pos hn hp
  have hz : 1 + D * b * Hslope n p ≠ 0 := ne_of_gt (by positivity)
  field_simp [hz]
  ring

theorem hasStrictDerivAt_focal_kernel_ownImpact {ι : Type*} [Fintype ι]
    {n : ℕ} (hn : 2 ≤ n) (rivals : ι → ℝ) (hr : ∀ j, 0 < rivals j)
    (f : ℝ → ℝ) {b L c : ℝ} (hb : 0 < b) (hL : 0 < L)
    (hcap : kernel n b L + ∑ j, kernel n (rivals j) L = c)
    (hi : kernel n b L ∈ Ioo (0 : ℝ) 1)
    (hclip0 : ∀ j, rivals j ≠ L) (hclip1 : ∀ j, rivals j ≠ (n : ℝ) * L)
    (hroot : ∀ x, 0 < x → ∃ T, 0 < T ∧ f x = kernel n x T ∧
      kernel n x T + ∑ j, kernel n (rivals j) T = c) :
    HasStrictDerivAt f
      (H n (kernel n b L) / (b * Hslope n (kernel n b L)) *
        (1 - focalWeight n b (kernel n b L) (rivalSensitivity n rivals L))) b := by
  have hh := hasStrictDerivAt_focal_kernel hn rivals hr f hb hL hcap hi hclip0 hclip1 hroot
  have hD : 0 ≤ rivalSensitivity n rivals L := by
    classical
    apply sum_nonneg
    intro j _
    split_ifs with hj
    · exact (sensitivity_pos hn (hr j) ⟨hj.1.le, hj.2.le⟩).le
    · exact le_rfl
  rwa [focal_derivative_weight_identity hn hb ⟨hi.1.le, hi.2.le⟩ hD] at hh

theorem focal_success_derivative_ownImpact {ι : Type*} [Fintype ι]
    {n : ℕ} (hn : 2 ≤ n) (rivals : ι → ℝ) (hr : ∀ j, 0 < rivals j)
    (f : ℝ → ℝ) {b L c : ℝ} (hb : 0 < b) (hL : 0 < L)
    (hcap : kernel n b L + ∑ j, kernel n (rivals j) L = c)
    (hi : kernel n b L ∈ Ioo (0 : ℝ) 1)
    (hclip0 : ∀ j, rivals j ≠ L) (hclip1 : ∀ j, rivals j ≠ (n : ℝ) * L)
    (hroot : ∀ x, 0 < x → ∃ T, 0 < T ∧ f x = kernel n x T ∧
      kernel n x T + ∑ j, kernel n (rivals j) T = c) :
    b * deriv (fun x => success n (f x)) b =
      ((n : ℝ) * (1 - kernel n b L) ^ (n - 1) * H n (kernel n b L) /
        Hslope n (kernel n b L)) *
          (1 - focalWeight n b (kernel n b L) (rivalSensitivity n rivals L)) := by
  have hf := hasStrictDerivAt_focal_kernel_ownImpact hn rivals hr f hb hL hcap hi hclip0 hclip1 hroot
  obtain ⟨T, hT, hfb, hTc⟩ := hroot b hb
  have he : f b = kernel n b L :=
    hfb.trans (focal_kernel_eq_of_roots hn b rivals hT hL hTc hcap)
  have hs : HasDerivAt (success n) ((n : ℝ) * (1 - f b) ^ (n - 1)) (f b) := by
    have hh := (((hasDerivAt_id (f b)).const_sub 1).pow n).const_sub 1
    convert hh using 1 <;> first | rfl | (simp only [id_eq]; ring)
  have hcomp := hs.comp b hf.hasDerivAt
  change b * deriv (success n ∘ f) b = _
  rw [hcomp.deriv, he]
  field_simp [hb.ne']

theorem hasStrictDerivAt_focal_kernel_zero {ι : Type*} [Fintype ι]
    {n : ℕ} (hn : 2 ≤ n) (rivals : ι → ℝ) (f : ℝ → ℝ)
    {b L c : ℝ} (hb : 0 < b) (hL : 0 < L) (hbl : b < L)
    (hcap : kernel n b L + ∑ j, kernel n (rivals j) L = c)
    (hroot : ∀ x, 0 < x → ∃ T, 0 < T ∧ f x = kernel n x T ∧
      kernel n x T + ∑ j, kernel n (rivals j) T = c) : HasStrictDerivAt f 0 b := by
  have hk := kernel_of_le n hbl.le
  rw [hk, zero_add] at hcap
  apply (hasStrictDerivAt_const b (0 : ℝ)).congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hb, eventually_lt_nhds hbl] with x hx hxL
  obtain ⟨T, hT, hf, hTc⟩ := hroot x hx
  have hxcap : kernel n x L + ∑ j, kernel n (rivals j) L = c := by
    rw [kernel_of_le n hxL.le, zero_add, hcap]
  exact (kernel_of_le n hxL.le).symm.trans
    ((focal_kernel_eq_of_roots hn x rivals hL hT hxcap hTc).trans hf.symm)

theorem hasStrictDerivAt_focal_kernel_one {ι : Type*} [Fintype ι]
    {n : ℕ} (hn : 2 ≤ n) (rivals : ι → ℝ) (f : ℝ → ℝ)
    {b L c : ℝ} (hb : 0 < b) (hL : 0 < L) (hnb : (n : ℝ) * L < b)
    (hcap : kernel n b L + ∑ j, kernel n (rivals j) L = c)
    (hroot : ∀ x, 0 < x → ∃ T, 0 < T ∧ f x = kernel n x T ∧
      kernel n x T + ∑ j, kernel n (rivals j) T = c) : HasStrictDerivAt f 0 b := by
  rw [kernel_of_ge n hn hL hnb.le] at hcap
  apply (hasStrictDerivAt_const b (1 : ℝ)).congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hb, eventually_gt_nhds hnb] with x hx hnx
  obtain ⟨T, hT, hf, hTc⟩ := hroot x hx
  have hxcap : kernel n x L + ∑ j, kernel n (rivals j) L = c := by
    rw [kernel_of_ge n hn hL hnx.le, hcap]
  exact (kernel_of_ge n hn hL hnx.le).symm.trans
    ((focal_kernel_eq_of_roots hn x rivals hL hT hxcap hTc).trans hf.symm)

theorem focal_kernel_monotone {ι : Type*} [Fintype ι]
    {n : ℕ} (hn : 2 ≤ n) (rivals : ι → ℝ) {b a L T c : ℝ}
    (hb : 0 < b) (hba : b ≤ a) (hL : 0 < L) (hT : 0 < T)
    (hcapL : kernel n b L + ∑ j, kernel n (rivals j) L = c)
    (hcapT : kernel n a T + ∑ j, kernel n (rivals j) T = c) :
    kernel n b L ≤ kernel n a T := by
  have ha := hb.trans_le hba
  have hp := scalarThreshold_kernel n hn hb hL
  have hq := scalarThreshold_kernel n hn ha hT
  by_contra hnot
  have hqp := lt_of_not_ge hnot
  have hTL : T < L := by
    by_contra hh
    have hs := sum_le_sum (s := (Finset.univ : Finset ι))
      (fun j _ => KernelTailEvent.kernel_antitone_price hn hL hT (le_of_not_gt hh) (b := rivals j))
    linarith
  have hpr := scalar_price_le_of_pos n b L _ hp (hq.1.trans_lt hqp)
  have hqr := scalar_receipt_le_of_lt_one n a T _ hq (hqp.trans_le hp.2.1)
  have hH := H_antitone n _ _ hqp.le hp.2.1
  have hh := mul_le_mul hba hH (H_pos n (by omega) _ hp.1 hp.2.1).le ha.le
  linarith

theorem focal_kernel_increment_le {ι : Type*} [Fintype ι]
    {n : ℕ} (hn : 2 ≤ n) (rivals : ι → ℝ) {b a L T c : ℝ}
    (hb : 0 < b) (hba : b ≤ a) (hL : 0 < L) (hT : 0 < T)
    (hcapL : kernel n b L + ∑ j, kernel n (rivals j) L = c)
    (hcapT : kernel n a T + ∑ j, kernel n (rivals j) T = c) :
    kernel n a T - kernel n b L ≤ (n : ℝ) * (a - b) / b := by
  have ha := hb.trans_le hba
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hp := scalarThreshold_kernel n hn hb hL
  have hq := scalarThreshold_kernel n hn ha hT
  by_cases hpq : kernel n a T ≤ kernel n b L
  · exact (sub_nonpos.mpr hpq).trans (div_nonneg (mul_nonneg hnR.le (sub_nonneg.mpr hba)) hb.le)
  have hpq := lt_of_not_ge hpq
  have hLT : L ≤ T := by
    by_contra hh
    have hs := sum_le_sum (s := (Finset.univ : Finset ι))
      (fun j _ => KernelTailEvent.kernel_antitone_price hn hT hL (le_of_lt (lt_of_not_ge hh)) (b := rivals j))
    linarith
  have hpr := scalar_receipt_le_of_lt_one n b L _ hp (hpq.trans_le hq.2.1)
  have hqr := scalar_price_le_of_pos n a T _ hq (hp.1.trans_lt hpq)
  have hgap := mul_le_mul_of_nonneg_left
    (H_decrease_lower n hn _ _ hpq.le hq.2.1) hb.le
  have hscale := mul_le_mul_of_nonneg_left (H_bounds n (by omega) _ hq.1 hq.2.1).2
    (sub_nonneg.mpr hba)
  have hh : b * ((kernel n a T - kernel n b L) / n) ≤ a - b := by nlinarith
  have hh' : b * (kernel n a T - kernel n b L) ≤ (a - b) * n := by
    apply (div_le_iff₀ hnR).mp
    simpa only [mul_div_assoc] using hh
  apply (le_div_iff₀ hb).mpr
  nlinarith

theorem focal_kernel_abs_sub_le {ι : Type*} [Fintype ι]
    {n : ℕ} (hn : 2 ≤ n) (rivals : ι → ℝ) (f : ℝ → ℝ) {c ε : ℝ} (hε : 0 < ε)
    (hroot : ∀ x, 0 < x → ∃ T, 0 < T ∧ f x = kernel n x T ∧
      kernel n x T + ∑ j, kernel n (rivals j) T = c)
    {x y : ℝ} (hx : ε ≤ x) (hy : ε ≤ y) :
    |f x - f y| ≤ ((n : ℝ) / ε) * |x - y| := by
  have hdir {x y : ℝ} (hx : ε ≤ x) (hy : ε ≤ y) (hxy : x ≤ y) :
      |f x - f y| ≤ ((n : ℝ) / ε) * |x - y| := by
    obtain ⟨L, hL, hfL, hLc⟩ := hroot x (hε.trans_le hx)
    obtain ⟨T, hT, hfT, hTc⟩ := hroot y (hε.trans_le hy)
    rw [hfL, hfT]
    have hm := focal_kernel_monotone hn rivals (hε.trans_le hx) hxy hL hT hLc hTc
    rw [abs_of_nonpos (sub_nonpos.mpr hm), abs_of_nonpos (sub_nonpos.mpr hxy)]
    have hh := focal_kernel_increment_le hn rivals (hε.trans_le hx) hxy hL hT hLc hTc
    have hdiv := div_le_div_of_nonneg_left (Nat.cast_nonneg n) hε hx
    have hmul := mul_le_mul_of_nonneg_right hdiv (sub_nonneg.mpr hxy)
    have he : (n : ℝ) * (y - x) / x = ((n : ℝ) / x) * (y - x) := by ring
    rw [he] at hh
    linarith
  rcases le_total x y with hxy | hyx
  · exact hdir hx hy hxy
  · simpa only [abs_sub_comm] using hdir hy hx hyx

theorem success_abs_sub_le (n : ℕ) {p q : ℝ}
    (hp : p ∈ Icc (0 : ℝ) 1) (hq : q ∈ Icc (0 : ℝ) 1) :
    |success n p - success n q| ≤ (n : ℝ) * |p - q| := by
  have hmax : max |1 - p| |1 - q| ≤ (1 : ℝ) := by
    rw [abs_of_nonneg (sub_nonneg.mpr hp.2), abs_of_nonneg (sub_nonneg.mpr hq.2)]
    exact max_le (by linarith [hp.1]) (by linarith [hq.1])
  have hpow : max |1 - p| |1 - q| ^ (n - 1) ≤ (1 : ℝ) :=
    pow_le_one₀ (le_max_of_le_left (abs_nonneg _)) hmax
  have hh := abs_pow_sub_pow_le (1 - p) (1 - q) n
  have hd : |(1 - p) - (1 - q)| = |p - q| := by
    have he : (1 - p) - (1 - q) = -(p - q) := by ring
    rw [he, abs_neg]
  rw [hd] at hh
  have hmul := mul_le_mul_of_nonneg_left hpow (mul_nonneg (abs_nonneg (p - q)) (Nat.cast_nonneg n))
  have he : |success n p - success n q| = |(1 - p) ^ n - (1 - q) ^ n| := by
    have hs : success n p - success n q = -((1 - p) ^ n - (1 - q) ^ n) := by unfold success; ring
    rw [hs, abs_neg]
  rw [he]
  nlinarith

theorem focal_success_lipschitzOn {ι : Type*} [Fintype ι]
    {n : ℕ} (hn : 2 ≤ n) (rivals : ι → ℝ) (f : ℝ → ℝ) {c ε : ℝ} (hε : 0 < ε)
    (hroot : ∀ x, 0 < x → ∃ T, 0 < T ∧ f x = kernel n x T ∧
      kernel n x T + ∑ j, kernel n (rivals j) T = c) :
    LipschitzOnWith (Real.nnabs ((n : ℝ) ^ 2 / ε)) (fun x => success n (f x)) (Ici ε) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  have hp (z : ℝ) (hz : ε ≤ z) : f z ∈ Icc (0 : ℝ) 1 := by
    obtain ⟨T, hT, he, _⟩ := hroot z (hε.trans_le hz)
    rw [he]
    exact ⟨kernel_nonneg n hn (hε.trans_le hz) hT, kernel_le_one n hn (hε.trans_le hz) hT⟩
  have h1 := success_abs_sub_le n (hp x hx) (hp y hy)
  have h2 := mul_le_mul_of_nonneg_left (focal_kernel_abs_sub_le hn rivals f hε hroot hx hy)
    (Nat.cast_nonneg n)
  rw [Real.dist_eq, Real.dist_eq, Real.coe_nnabs,
    abs_of_nonneg (div_nonneg (sq_nonneg _) hε.le)]
  have he : (n : ℝ) * ((n : ℝ) / ε * |x - y|) = (n : ℝ) ^ 2 / ε * |x - y| := by ring
  exact h1.trans (he ▸ h2)

end FCAppendix.PayOnce.OwnImpact
