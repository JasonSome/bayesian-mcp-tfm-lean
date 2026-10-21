import FCAppendix.Affine.Uniform06.EntryParityRenewal

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.EntryConditionalRelative
open Set Filter Topology
open FCAppendix.PiBinomial
open FCAppendix.Affine.WeightedSampling
open FCAppendix.Affine.Uniform06.WeightedMoments
open FCAppendix.Affine.Uniform06.EntryUntilting
open FCAppendix.Affine.Uniform06.EntryRenewal
open FCAppendix.Affine.Uniform06.EntryParity
open FCAppendix.Affine.Uniform06.EntryParityRenewal
open scoped BigOperators

lemma potential_pos (k : ℕ) {s : ℝ} (hs : 0 < s) : 0 < potential k s := by
  unfold potential
  rw [max_eq_left hs.le]
  positivity

lemma potential_ratio (k : ℕ) {s C : ℝ} (hs : 0 < s) (hsC : 0 ≤ s+C) :
    potential k (s+C)/potential k s=(1+C/s)^(k+1) := by
  have hk : (k : ℝ)+1 ≠ 0 := by positivity
  calc
    potential k (s+C)/potential k s=((s+C)/s)^(k+1) := by
      rw [potential,potential,max_eq_left hsC,max_eq_left hs.le,div_pow]
      field_simp [hs.ne',hk]
    _ = (1+C/s)^(k+1) := by
      congr 1
      field_simp [hs.ne']

lemma moment_potential_ratio (k : ℕ) {s : ℝ} (hs : 0 < s) :
    deficitMoment k s/potential k s=((k : ℝ)+1)/s := by
  have hk : (k : ℝ)+1 ≠ 0 := by positivity
  by_cases hk0 : k=0
  · subst k
    simp [deficitMoment,potential,hs,max_eq_left hs.le]
  · simp only [deficitMoment,if_neg hk0,potential,max_eq_left hs.le,pow_succ]
    field_simp [hs.ne',hk,pow_ne_zero k hs.ne']

lemma normalized_sandwich {M P F Fl Fu R μ δ E : ℝ}
    (hP : 0 < P) (hF : 0 < F) (hμ : 0 < μ) (hplus : 0 < μ+δ) (hminus : 0 < μ-δ)
    (hl : P*(1-E)*Fl/(μ+δ)-P*R ≤ M) (hu : M ≤ P*Fu/(μ-δ)) :
    (1-E)*(μ/(μ+δ))*(Fl/F)-μ*(R/F) ≤ M/(P*F/μ) ∧
      M/(P*F/μ) ≤ (μ/(μ-δ))*(Fu/F) := by
  have hden : 0 < P*F/μ := by positivity
  constructor
  · have h := div_le_div_of_nonneg_right hl hden.le
    convert! h using 1
    field_simp [hP.ne',hF.ne',hμ.ne',hplus.ne']
  · have h := div_le_div_of_nonneg_right hu hden.le
    convert! h using 1
    field_simp [hP.ne',hF.ne',hμ.ne',hminus.ne']

lemma plus_ratio_bounds {a μ δ : ℝ} (ha : 0 < a) (hμ : a ≤ μ) (hδ : 0 ≤ δ) :
    μ/(μ+δ) ∈ Icc (0:ℝ) 1 ∧ 1-μ/(μ+δ) ≤ δ/a := by
  have hm : 0 < μ+δ := by linarith
  constructor
  · exact ⟨div_nonneg (ha.le.trans hμ) hm.le,(div_le_one hm).mpr (by linarith)⟩
  · have he : 1-μ/(μ+δ)=δ/(μ+δ) := by field_simp [hm.ne']; ring
    rw [he]
    exact div_le_div_of_nonneg_left hδ ha (by linarith)

lemma minus_ratio_bounds {a μ δ : ℝ} (ha : 0 < a) (hμ : a ≤ μ)
    (hδ : 0 ≤ δ) (hsmall : δ ≤ a/2) :
    0 ≤ μ/(μ-δ) ∧ μ/(μ-δ) ≤ 2 ∧ μ/(μ-δ)-1 ≤ 2*δ/a := by
  have hm : 0 < μ-δ := by linarith
  have hma : a/2 ≤ μ-δ := by linarith
  refine ⟨div_nonneg (ha.le.trans hμ) hm.le,?_,?_⟩
  · apply (div_le_iff₀ hm).mpr
    linarith
  · have he : μ/(μ-δ)-1=δ/(μ-δ) := by field_simp [hm.ne']; ring
    rw [he]
    have ht := div_le_div_of_nonneg_left hδ (by linarith : 0 < a/2) hma
    convert! ht using 1
    ring

lemma small_power_bounds {k : ℕ} (hk : k ≤ 2) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    (1-t)^(k+1) ∈ Icc (0:ℝ) 1 ∧ 1-(1-t)^(k+1) ≤ 3*t ∧
    1 ≤ (1+2*t)^(k+1) ∧ (1+2*t)^(k+1)-1 ≤ 26*t := by
  have ht2 : t^2 ≤ t := by nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr ht.2)]
  have ht3 : t^3 ≤ t^2 := by nlinarith [mul_nonneg (sq_nonneg t) (sub_nonneg.mpr ht.2)]
  refine ⟨⟨pow_nonneg (sub_nonneg.mpr ht.2) _,?_⟩,?_,?_,?_⟩
  all_goals
    interval_cases k <;> norm_num only [zero_add,pow_one,Nat.reduceAdd] <;>
      nlinarith [sq_nonneg t]

lemma product_defect_le {x y z : ℝ} (hx : x ∈ Icc (0:ℝ) 1)
    (hy : y ∈ Icc (0:ℝ) 1) (hz : z ∈ Icc (0:ℝ) 1) :
    1-x*y*z ≤ (1-x)+(1-y)+(1-z) := by
  have hxy : x*y ≤ 1 := by
    calc
      x*y ≤ 1*y := mul_le_mul_of_nonneg_right hx.2 hy.1
      _ ≤ 1 := by simpa only [one_mul] using hy.2
  nlinarith [mul_nonneg (sub_nonneg.mpr hx.2) (sub_nonneg.mpr hy.2),
    mul_nonneg (sub_nonneg.mpr hxy) (sub_nonneg.mpr hz.2)]

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem relative_error_bound (w : Weights ι) (h : ι → ℝ)
    {a A : ℝ} (ha : 0 < a) (hh : ∀ i, h i ∈ Icc a A)
    {n J K k e : ℕ} (hn : 0 < n) (he : e ≤ 1) (hk : k ≤ 2)
    (hJn : J ≤ n+1) (hK : 2*J+1 ≤ K)
    (hW : 0 < totalWeight w) (hhalf : 2*(K : ℝ) ≤ totalWeight w)
    {s : ℝ} (hsA : A < s) (hs : s ≤ 2*a*J)
    (hsmall : (J : ℝ)*((J : ℝ)+e)/n ≤ 1)
    (hdrift : 4*A*K/totalWeight w ≤ a/2) :
    |fairMoment w h (2*n+e) k s /
        (pmf (2*n+e) (1/2) (n+e)*potential k s/weightedMean w h)-1| ≤
      (J : ℝ)*((J : ℝ)+e)/n+2*(4*A*K/totalWeight w)/a+52*A/s := by
  let μ := weightedMean w h
  let δ := 4*A*K/totalWeight w
  let E := (J : ℝ)*((J : ℝ)+e)/n
  let t := A/s
  have hμ := weightedMean_bounds w h hh hW
  have hA : 0 ≤ A := (ha.le.trans hμ.1).trans hμ.2
  have hs0 : 0 < s := by linarith
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hδμ : δ < μ := by dsimp [δ,μ]; linarith [hμ.1]
  have hP : 0 < pmf (2*n+e) (1/2) (n+e) := by
    rw [pmf_half_eq_choose_div]
    apply div_pos
    · exact_mod_cast Nat.choose_pos (show n+e ≤ 2*n+e by omega)
    · positivity
  have hb := finite_conditional_moment_bounds w h ha hh hn he hk hJn hK hW hhalf hs hsmall hδμ
  have hr := normalized_sandwich hP (potential_pos k hs0) (ha.trans_le hμ.1)
    (by dsimp [μ,δ]; linarith [hμ.1,hδ]) (sub_pos.mpr hδμ) hb.1 hb.2
  have hpminus := potential_ratio k hs0 (show 0 ≤ s+(-A) by linarith)
  have hpplus := potential_ratio k hs0 (show 0 ≤ s+2*A by positivity)
  have hmratio := moment_potential_ratio k hs0
  have hminusid : 1+(-A)/s=1-t := by dsimp [t]; ring
  have hplusid : 1+(2*A)/s=1+2*t := by dsimp [t]; ring
  rw [show s+(-A)=s-A by ring,hminusid] at hpminus
  rw [hplusid] at hpplus
  rw [hpminus,hpplus,hmratio] at hr
  have ht : t ∈ Icc (0:ℝ) 1 := by
    dsimp [t]
    exact ⟨div_nonneg hA hs0.le,(div_le_one hs0).mpr hsA.le⟩
  have hE : E ∈ Icc (0:ℝ) 1 := ⟨by dsimp [E]; positivity,hsmall⟩
  have hplus := plus_ratio_bounds ha hμ.1 hδ
  have hminus := minus_ratio_bounds ha hμ.1 hδ hdrift
  have hpow := small_power_bounds hk ht
  have hprod := product_defect_le
    (show 1-E ∈ Icc (0:ℝ) 1 by constructor <;> linarith [hE.1,hE.2]) hplus.1 hpow.1
  have hcorr : μ*(((k : ℝ)+1)/s) ≤ 3*t := by
    have hkR : (k : ℝ)+1 ≤ 3 := by exact_mod_cast (show k+1 ≤ 3 by omega)
    have hmul : μ*((k : ℝ)+1) ≤ 3*A := by
      dsimp [μ]
      nlinarith [mul_nonneg hA (sub_nonneg.mpr hkR),mul_nonneg ((by positivity : (0:ℝ) ≤ (k : ℝ)+1))
        (sub_nonneg.mpr hμ.2)]
    dsimp [t]
    convert! div_le_div_of_nonneg_right hmul hs0.le using 1 <;> ring
  have hupperprod : (μ/(μ-δ))*((1+2*t)^(k+1))-1 ≤ 2*δ/a+52*t := by
    have hm := mul_le_mul_of_nonneg_left hpow.2.2.2 hminus.1
    have hm2 := mul_le_mul_of_nonneg_right hminus.2.1 (show 0 ≤ 26*t by positivity)
    nlinarith [hminus.2.2]
  have hnorm : |fairMoment w h (2*n+e) k s /
      (pmf (2*n+e) (1/2) (n+e)*potential k s/μ)-1| ≤ E+2*(δ/a)+52*t := by
    rw [abs_le]
    constructor
    · have hlow : 1-((1-E)*(μ/(μ+δ))*(1-t)^(k+1)) ≤ E+δ/a+3*t := by
        nlinarith only [hprod,hplus.2,hpow.2.1]
      nlinarith only [hlow,hr.1,hcorr,div_nonneg hδ ha.le,ht.1]
    · have hup : (μ/(μ-δ))*((1+2*t)^(k+1))-1 ≤ 2*(δ/a)+52*t := by
        convert! hupperprod using 1
        ring
      nlinarith only [hr.2,hup,hE.1]
  convert! hnorm using 1
  dsimp only [E,μ,δ,t]
  ring

def stoppingPairs (a s : ℝ) : ℕ := ⌈s/(2*a)⌉₊+1

lemma stoppingPairs_bounds {a s : ℝ} (ha : 0 < a) (hs : 0 ≤ s) :
    s ≤ 2*a*(stoppingPairs a s : ℝ) ∧
      (stoppingPairs a s : ℝ) ≤ s/(2*a)+2 := by
  have hlo := Nat.le_ceil (s/(2*a))
  have hup := Nat.ceil_lt_add_one (div_nonneg hs (by positivity : 0 ≤ 2*a))
  have hpa : 0 < 2*a := by positivity
  have hs' : s ≤ (2*a)*(⌈s/(2*a)⌉₊ : ℝ) := by nlinarith [(div_le_iff₀ hpa).mp hlo]
  simp only [stoppingPairs,Nat.cast_add_one]
  constructor <;> nlinarith

theorem conditional_relative_tendsto
    {κ : ℕ → Type*} [∀ m, Fintype (κ m)] [∀ m, DecidableEq (κ m)] [∀ m, Nonempty (κ m)]
    (w : (m : ℕ) → Weights (κ m)) (h : (m : ℕ) → κ m → ℝ)
    (n J K e : ℕ → ℕ) (s : ℕ → ℝ) {a A : ℝ} (ha : 0 < a)
    (hh : ∀ m i, h m i ∈ Icc a A) (he : ∀ m, e m ≤ 1) {k : ℕ} (hk : k ≤ 2)
    (hfinite : ∀ᶠ m in atTop,
      0 < n m ∧ J m ≤ n m+1 ∧ 2*J m+1 ≤ K m ∧ 0 < totalWeight (w m) ∧
      2*(K m : ℝ) ≤ totalWeight (w m) ∧ s m ≤ 2*a*J m)
    (hs : Tendsto s atTop atTop)
    (hE : Tendsto (fun m => (J m : ℝ)*((J m : ℝ)+e m)/n m) atTop (𝓝 0))
    (hδ : Tendsto (fun m => 4*A*K m/totalWeight (w m)) atTop (𝓝 0)) :
    Tendsto (fun m => fairMoment (w m) (h m) (2*n m+e m) k (s m)/
      (pmf (2*n m+e m) (1/2) (n m+e m)*potential k (s m)/weightedMean (w m) (h m))-1)
      atTop (𝓝 0) := by
  have hsmall := hE.eventually_le_const (show (0:ℝ) < 1 by norm_num)
  have hdrift := hδ.eventually_le_const (show (0:ℝ) < a/2 by positivity)
  have herror : Tendsto (fun m => (J m : ℝ)*((J m : ℝ)+e m)/n m+
      2*(4*A*K m/totalWeight (w m))/a+52*A/s m) atTop (𝓝 0) := by
    have htail : Tendsto (fun m => 52*A/s m) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hs
    convert! (hE.add ((hδ.const_mul 2).div_const a)).add htail using 1
    norm_num
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ herror
  filter_upwards [hfinite,hs.eventually_gt_atTop A,hsmall,hdrift] with m hm hmA hmE hmδ
  rcases hm with ⟨hmn,hmJ,hmK,hmW,hmhalf,hms⟩
  simpa only [Real.norm_eq_abs] using relative_error_bound (w m) (h m) ha (hh m)
    hmn (he m) hk hmJ hmK hmW hmhalf hmA hms hmE hmδ

end FCAppendix.Affine.Uniform06.EntryConditionalRelative
