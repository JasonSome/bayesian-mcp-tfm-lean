import FCAppendix.Affine.Uniform06.EntryRawSignMoments

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.EntryModerateWindow

open Set Filter Topology
open FCAppendix.Affine.WeightedSampling FCAppendix.PiBinomial
open EntryParity EntryRenewal EntryParityRenewal EntryConditionalRelative WeightedMoments
open scoped BigOperators

lemma bounded_div_sqrt_zero (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (e : ℕ → ℕ) (he : ∀ m,e m ≤ 1) :
    Tendsto (fun m => (e m:ℝ)/Real.sqrt (N m:ℝ)) atTop (𝓝 0) := by
  have hs : Tendsto (fun m => Real.sqrt (N m:ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp hN)
  exact squeeze_zero (fun _ => by positivity)
    (fun m => div_le_div_of_nonneg_right (show (e m : ℝ) ≤ 1 by exact_mod_cast he m) (Real.sqrt_nonneg _))
    (tendsto_const_nhds.div_atTop hs)

lemma moderate_window_geometry (N : ℕ → ℕ) (hNp : ∀ m,0 < N m)
    (_hN : Tendsto N atTop atTop) (θ W : ℕ → ℝ)
    (hθp : ∀ᶠ m in atTop,0 < θ m) (hθ : Tendsto θ atTop (𝓝 0))
    (hθN : Tendsto (fun m => θ m*Real.sqrt (N m:ℝ)) atTop atTop)
    {ε M : ℝ} (hε : 0 < ε) (_hM : 0 < M)
    (hwindow : ∀ m,ε ≤ θ m*W m ∧ θ m*W m ≤ M) :
    Tendsto W atTop atTop ∧ Tendsto (fun m => W m/Real.sqrt (N m:ℝ)) atTop (𝓝 0) := by
  have hWp : ∀ᶠ m in atTop,0 < W m := by
    filter_upwards [hθp] with m hm
    have hh := hε.trans_le (hwindow m).1
    nlinarith only [hh,hm]
  have hW : Tendsto W atTop atTop := by
    apply tendsto_atTop.mpr
    intro R
    have hden : 0 < max R 0+1 := by positivity
    filter_upwards [hθp,hθ.eventually_lt_const (div_pos hε hden)] with m hm hsmall
    have hh : θ m*(max R 0+1) < ε := (lt_div_iff₀ hden).mp hsmall
    have hw : max R 0+1 < W m := (mul_lt_mul_iff_right₀ hm).mp (hh.trans_le (hwindow m).1)
    exact (le_max_left R 0).trans (by linarith)
  have hupper : Tendsto (fun m => M/(θ m*Real.sqrt (N m:ℝ))) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hθN
  have hratio : Tendsto (fun m => W m/Real.sqrt (N m:ℝ)) atTop (𝓝 0) := by
    apply squeeze_zero' (hWp.mono fun m hm => div_nonneg hm.le (Real.sqrt_nonneg _)) ?_ hupper
    filter_upwards [hθp] with m hm
    have hs : 0 < Real.sqrt (N m:ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hNp m)
    apply (div_le_div_iff₀ hs (mul_pos hm hs)).mpr
    nlinarith only [mul_le_mul_of_nonneg_right (hwindow m).2 hs.le]
  exact ⟨hW,hratio⟩

def peakConstant (τ : ℝ) : ℝ := (1/Real.sqrt Real.pi)/Real.sqrt (τ/2)

theorem peak_constant_pos {τ : ℝ} (hτ : 0 < τ) : 0 < peakConstant τ := by
  unfold peakConstant
  positivity

section Sequences
variable {κ : ℕ → Type*} [∀ m,Fintype (κ m)] [∀ m,DecidableEq (κ m)] [∀ m,Nonempty (κ m)]

theorem conditional_coefficient_tendsto
    (w : (m : ℕ) → Weights (κ m)) (h : (m : ℕ) → κ m → ℝ)
    (N H : ℕ → ℕ) (hNp : ∀ m,0 < N m) (hN : Tendsto N atTop atTop)
    (θ W : ℕ → ℝ) (hθp : ∀ᶠ m in atTop,0 < θ m)
    (hθ : Tendsto θ atTop (𝓝 0))
    (hθN : Tendsto (fun m => θ m*Real.sqrt (N m:ℝ)) atTop atTop)
    {a A τ v μ ε M : ℝ} (ha : 0 < a) (hτ : 0 < τ) (hv : 0 < v) (hμ : 0 < μ)
    (hε : 0 < ε) (hM : 0 < M) (hh : ∀ m j,h m j∈Icc a A)
    (hH : Tendsto (fun m => (H m:ℝ)/(N m:ℝ)) atTop (𝓝 τ))
    (hw : Tendsto (fun m => totalWeight (w m)/(N m:ℝ)) atTop (𝓝 v))
    (hm : Tendsto (fun m => weightedMean (w m) (h m)) atTop (𝓝 μ))
    (hwindow : ∀ m,ε ≤ θ m*W m ∧ θ m*W m ≤ M)
    {k : ℕ} (hk : k ≤ 2) :
    Tendsto (fun m => Real.sqrt (N m:ℝ)*fairMoment (w m) (h m) (H m) k (W m)/
      (W m)^(k+1)) atTop (𝓝 (peakConstant τ/(((k:ℝ)+1)*μ))) := by
  let n := fun m => H m/2
  let e := fun m => H m%2
  let J := fun m => stoppingPairs a (W m)
  let K := fun m => 2*J m+1
  have he (m) : e m ≤ 1 := by dsimp [e]; omega
  have hHe (m) : 2*n m+e m=H m := by dsimp [n,e]; omega
  have hNr (m) : (0:ℝ)< N m := by exact_mod_cast hNp m
  have hsNp (m) : 0 < Real.sqrt (N m:ℝ) := Real.sqrt_pos.mpr (hNr m)
  have hsN : Tendsto (fun m => Real.sqrt (N m:ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp hN)
  have heN : Tendsto (fun m => (e m:ℝ)/(N m:ℝ)) atTop (𝓝 0) :=
    squeeze_zero (fun _ => by positivity)
      (fun m => div_le_div_of_nonneg_right (show (e m : ℝ) ≤ 1 by exact_mod_cast he m) (hNr m).le)
      (tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp hN))
  have hnN : Tendsto (fun m => (n m:ℝ)/(N m:ℝ)) atTop (𝓝 (τ/2)) := by
    have hlim := (hH.sub heN).div_const 2
    simp only [sub_zero] at hlim
    apply hlim.congr
    intro m
    have hhR : 2*(n m:ℝ)+e m=H m := by exact_mod_cast hHe m
    field_simp [(hNr m).ne']
    linarith
  have hnTop : Tendsto n atTop atTop := by
    have hprod := (tendsto_natCast_atTop_atTop.comp hN).atTop_mul_pos (by positivity : 0 < τ/2) hnN
    have hreal : Tendsto (fun m => (n m:ℝ)) atTop atTop := by
      apply hprod.congr
      intro m
      simp only [Function.comp_def]
      field_simp [(hNr m).ne']
    apply tendsto_atTop.mpr
    intro K
    filter_upwards [hreal.eventually_ge_atTop (K:ℝ)] with m hm
    exact_mod_cast hm
  have hW := moderate_window_geometry N hNp hN θ W hθp hθ hθN hε hM hwindow
  have hJlow (m) : 1 ≤ J m := by dsimp [J,stoppingPairs]; omega
  have hJN : Tendsto (fun m => (J m:ℝ)/Real.sqrt (N m:ℝ)) atTop (𝓝 0) := by
    have hr : Tendsto (fun m => (W m/Real.sqrt (N m:ℝ))/(2*a)+2/Real.sqrt (N m:ℝ))
        atTop (𝓝 0) := by simpa using (hW.2.div_const (2*a)).add (tendsto_const_nhds.div_atTop hsN)
    apply squeeze_zero' (Eventually.of_forall fun _ => by positivity) ?_ hr
    filter_upwards [hW.1.eventually_ge_atTop 0] with m hm
    have hhJ := (stoppingPairs_bounds ha hm).2
    have hh := div_le_div_of_nonneg_right hhJ (hsNp m).le
    convert! hh using 1
    ring
  have heRoot := bounded_div_sqrt_zero N hN e he
  have hE : Tendsto (fun m => (J m:ℝ)*((J m:ℝ)+e m)/(n m:ℝ)) atTop (𝓝 0) := by
    have hlim := (hJN.mul (hJN.add heRoot)).div hnN (by positivity : τ/2≠0)
    simp only [zero_add,mul_zero,zero_div] at hlim
    apply hlim.congr'
    filter_upwards [hnTop.eventually_gt_atTop 0] with m hnm
    have hnr : (0:ℝ)< n m := by exact_mod_cast hnm
    have hsq := Real.sq_sqrt (hNr m).le
    dsimp only [Pi.div_apply,Pi.mul_apply]
    field_simp [hnr.ne',(hNr m).ne',(hsNp m).ne']
    nlinarith [congrArg (fun z : ℝ => (J m:ℝ)*((J m:ℝ)+e m)*z) hsq]
  have hKNroot : Tendsto (fun m => (K m:ℝ)/Real.sqrt (N m:ℝ)) atTop (𝓝 0) := by
    have hh := (hJN.const_mul 2).add (tendsto_const_nhds.div_atTop hsN :
      Tendsto (fun m => 1/Real.sqrt (N m:ℝ)) atTop (𝓝 0))
    simpa only [K,Nat.cast_add_one,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_zero,zero_add,one_add_one_eq_two,add_div,mul_div_assoc,add_zero,mul_zero] using hh
  have hKN : Tendsto (fun m => (K m:ℝ)/(N m:ℝ)) atTop (𝓝 0) := by
    have hh := hKNroot.mul (tendsto_const_nhds.div_atTop hsN :
      Tendsto (fun m => 1/Real.sqrt (N m:ℝ)) atTop (𝓝 0))
    simp only [mul_zero] at hh
    apply hh.congr
    intro m
    rw [div_mul_div_comm,mul_one,← sq,Real.sq_sqrt (hNr m).le]
  have hKW : Tendsto (fun m => (K m:ℝ)/totalWeight (w m)) atTop (𝓝 0) := by
    have hh := hKN.div hw hv.ne'
    simp only [zero_div] at hh
    apply hh.congr
    intro m
    dsimp only [Pi.div_apply]
    exact div_div_div_cancel_right₀ (hNr m).ne' _ _
  have hδ : Tendsto (fun m => 4*A*K m/totalWeight (w m)) atTop (𝓝 0) := by
    simpa only [mul_div_assoc,mul_zero] using hKW.const_mul (4*A)
  have hfinite : ∀ᶠ m in atTop,
      0 < n m ∧ J m ≤ n m+1 ∧ 2*J m+1 ≤ K m ∧ 0 < totalWeight (w m) ∧
      2*(K m:ℝ) ≤ totalWeight (w m) ∧ W m ≤ 2*a*J m := by
    filter_upwards [hnTop.eventually_gt_atTop 0,hE.eventually_le_const (by norm_num : (0:ℝ)<1),
      hw.eventually_const_lt hv,hKW.eventually_le_const (by norm_num : (0:ℝ)<1/2),
      hW.1.eventually_ge_atTop 0] with m hnm hmE hwpos hmK hmW
    have hnr : (0:ℝ)< n m := by exact_mod_cast hnm
    have hWpos : 0 < totalWeight (w m) := (div_pos_iff_of_pos_right (hNr m)).mp hwpos
    have hJ1 : (1:ℝ) ≤ J m := by exact_mod_cast hJlow m
    have hnJ : (J m:ℝ) ≤ n m := by
      have hhE := (div_le_one hnr).mp hmE
      nlinarith [(show (0:ℝ) ≤ e m from Nat.cast_nonneg (e m)),mul_nonneg (Nat.cast_nonneg (α := ℝ) (J m)) (Nat.cast_nonneg (α := ℝ) (e m))]
    refine ⟨hnm,by
      have hjn : J m ≤ n m := by exact_mod_cast hnJ
      omega,le_rfl,hWpos,?_,
      (stoppingPairs_bounds ha hmW).1⟩
    have hhK := (div_le_iff₀ hWpos).mp hmK
    linarith
  have hrelative := conditional_relative_tendsto w h n J K e W ha hh he hk hfinite hW.1 hE hδ
  have hratio : Tendsto (fun m => fairMoment (w m) (h m) (H m) k (W m)/
      (pmf (H m) (1/2) (n m+e m)*potential k (W m)/weightedMean (w m) (h m))) atTop (𝓝 1) := by
    simp_rw [hHe] at hrelative
    simpa only [sub_add_cancel,zero_add] using hrelative.add_const 1
  have hpeak := peak_mul_sqrt_tendsto n e hnTop he
  have hP : Tendsto (fun m => pmf (H m) (1/2) (n m+e m)*Real.sqrt (N m:ℝ))
      atTop (𝓝 (peakConstant τ)) := by
    have hh := hpeak.div hnN.sqrt (ne_of_gt (Real.sqrt_pos.mpr (by positivity : 0 < τ/2)))
    change Tendsto _ atTop (𝓝 (peakConstant τ)) at hh
    apply hh.congr'
    filter_upwards [hnTop.eventually_gt_atTop 0] with m hnm
    have hnr : (0:ℝ)< n m := by exact_mod_cast hnm
    dsimp only [Pi.div_apply]
    rw [hHe,Real.sqrt_div hnr.le]
    field_simp [(Real.sqrt_pos.mpr hnr).ne',(hsNp m).ne']
  have hlim := (hratio.mul hP).div (hm.const_mul ((k:ℝ)+1))
    (mul_ne_zero (by positivity) hμ.ne')
  simp only [one_mul] at hlim
  apply hlim.congr'
  filter_upwards [hfinite,hW.1.eventually_gt_atTop 0] with m hmfin hmW
  have hmean : 0 < weightedMean (w m) (h m) := ha.trans_le (weightedMean_bounds _ _ (hh m) hmfin.2.2.2.1).1
  have hp : 0 < pmf (H m) (1/2) (n m+e m) := by
    rw [← hHe m,pmf_half_eq_choose_div]
    apply div_pos
    · exact_mod_cast Nat.choose_pos (show n m+e m ≤ 2*n m+e m by omega)
    · positivity
  dsimp only [Pi.div_apply]
  rw [EntryRenewal.potential,max_eq_left hmW.le]
  field_simp [hp.ne',hmean.ne',pow_ne_zero (k+1) hmW.ne',show (k:ℝ)+1≠0 by positivity]

end Sequences

theorem uniform_of_all_sequences {Ξ : ℕ → Type*} (G : (m : ℕ) → Set (Ξ m))
    (F : (m : ℕ) → Ξ m → ℝ) (L : ℝ)
    (hseq : ∀ (n : ℕ → ℕ),Tendsto n atTop atTop → ∀ (x : (m : ℕ) → Ξ (n m)),
      (∀ m,x m∈G (n m)) → Tendsto (fun m => F (n m) (x m)) atTop (𝓝 L)) :
    ∀ ε > 0, ∀ᶠ m in atTop,∀ x∈G m,|F m x-L| < ε := by
  intro ε hε
  by_contra hnot
  have hbad : ∀ M : ℕ,∃ m ≥ M,∃ x : Ξ m,x∈G m ∧ ε ≤ |F m x-L| := by
    intro M
    by_contra hn
    apply hnot
    apply eventually_atTop.mpr
    refine ⟨M,?_⟩
    intro m hm x hx
    by_contra hsmall
    exact hn ⟨m,hm,x,hx,le_of_not_gt hsmall⟩
  choose n hn x hx using hbad
  have hnt : Tendsto n atTop atTop := tendsto_atTop_mono hn tendsto_id
  have hlim := (hseq n hnt x (fun m => (hx m).1)).sub_const L
  have hsmall := hlim.abs.eventually_lt_const (by simpa only [sub_self,abs_zero] using hε)
  obtain ⟨m,hm⟩ := hsmall.exists
  exact (not_lt_of_ge (hx m).2) hm

section UniformLists
variable {Ξ κ : ℕ → Type*} [∀ m,Fintype (κ m)]
    [∀ m,DecidableEq (κ m)] [∀ m,Nonempty (κ m)]

def ProfileWindow (w : (m : ℕ) → Ξ m → Weights (κ m))
    (h : (m : ℕ) → Ξ m → κ m → ℝ) (H : (m : ℕ) → Ξ m → ℕ)
    (W : (m : ℕ) → Ξ m → ℝ) (N : ℕ → ℕ) (θ e : ℕ → ℝ)
    (a A τ v μ ε M : ℝ) (m : ℕ) : Set (Ξ m) :=
  {x | (∀ j,h m x j∈Icc a A) ∧
    |(H m x:ℝ)/(N m:ℝ)-τ| ≤ e m ∧
    |totalWeight (w m x)/(N m:ℝ)-v| ≤ e m ∧
    |weightedMean (w m x) (h m x)-μ| ≤ e m ∧
    ε ≤ θ m*W m x ∧ θ m*W m x ≤ M}

theorem uniform_conditional_coefficient
    (w : (m : ℕ) → Ξ m → Weights (κ m)) (h : (m : ℕ) → Ξ m → κ m → ℝ)
    (H : (m : ℕ) → Ξ m → ℕ) (W : (m : ℕ) → Ξ m → ℝ)
    (N : ℕ → ℕ) (hNp : ∀ m,0 < N m) (hN : Tendsto N atTop atTop)
    (θ e : ℕ → ℝ) (hθp : ∀ᶠ m in atTop,0 < θ m)
    (hθ : Tendsto θ atTop (𝓝 0))
    (hθN : Tendsto (fun m => θ m*Real.sqrt (N m:ℝ)) atTop atTop)
    (he : Tendsto e atTop (𝓝 0))
    {a A τ v μ ε M : ℝ} (ha : 0 < a) (hτ : 0 < τ) (hv : 0 < v) (hμ : 0 < μ)
    (hε : 0 < ε) (hM : 0 < M) {k : ℕ} (hk : k ≤ 2) :
    ∀ δ > 0, ∀ᶠ m in atTop,∀ x∈ProfileWindow w h H W N θ e a A τ v μ ε M m,
      |Real.sqrt (N m:ℝ)*fairMoment (w m x) (h m x) (H m x) k (W m x)/
        (W m x)^(k+1)-peakConstant τ/(((k:ℝ)+1)*μ)| < δ := by
  apply uniform_of_all_sequences
    (ProfileWindow w h H W N θ e a A τ v μ ε M)
    (fun m x => Real.sqrt (N m:ℝ)*fairMoment (w m x) (h m x) (H m x) k (W m x)/(W m x)^(k+1))
    (peakConstant τ/(((k:ℝ)+1)*μ))
  intro n hn x hx
  have hH : Tendsto (fun m => (H (n m) (x m):ℝ)/(N (n m):ℝ)) atTop (𝓝 τ) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _) (fun m => ?_) (he.comp hn)
    simpa only [Real.norm_eq_abs,Function.comp_def] using! (hx m).2.1
  have hw : Tendsto (fun m => totalWeight (w (n m) (x m))/(N (n m):ℝ)) atTop (𝓝 v) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _) (fun m => ?_) (he.comp hn)
    simpa only [Real.norm_eq_abs,Function.comp_def] using! (hx m).2.2.1
  have hm : Tendsto (fun m => weightedMean (w (n m) (x m)) (h (n m) (x m))) atTop (𝓝 μ) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _) (fun m => ?_) (he.comp hn)
    simpa only [Real.norm_eq_abs,Function.comp_def] using! (hx m).2.2.2.1
  exact conditional_coefficient_tendsto (fun m => w (n m) (x m)) (fun m => h (n m) (x m))
    (fun m => N (n m)) (fun m => H (n m) (x m)) (fun m => hNp (n m)) (hN.comp hn)
    (fun m => θ (n m)) (fun m => W (n m) (x m)) (hn.eventually hθp) (hθ.comp hn)
    (hθN.comp hn) ha hτ hv hμ hε hM (fun m => (hx m).1) hH hw hm
    (fun m => (hx m).2.2.2.2) hk

end UniformLists

end FCAppendix.Affine.Uniform06.EntryModerateWindow
