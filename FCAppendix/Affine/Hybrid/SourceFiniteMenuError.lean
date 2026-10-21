import FCAppendix.Affine.Hybrid.SourceMenuNeighborhood

noncomputable section
namespace FCAppendix.Affine.Hybrid
open Set Filter Topology Classical

def reciprocalSamplingError (L : ℝ) (D : ℕ) : ℝ :=
  2*((1/L)/Real.sqrt (D : ℝ)+(1/L)/(D : ℝ))

lemma reciprocalSamplingError_tendsto_zero (L : ℝ) :
    Tendsto (reciprocalSamplingError L) atTop (𝓝 0) := by
  have hn : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hr : Tendsto (fun N : ℕ => Real.sqrt (N : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hn
  have hfirst : Tendsto (fun N : ℕ => (1/L)/Real.sqrt (N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hr
  have hsecond : Tendsto (fun N : ℕ => (1/L)/(N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hn
  change Tendsto (fun D : ℕ => 2*((1/L)/Real.sqrt (D : ℝ)+(1/L)/(D : ℝ))) atTop (𝓝 0)
  simpa only [mul_zero,add_zero] using (hfirst.add hsecond).const_mul 2

lemma eventually_linear_counts_large {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (T : ℕ) :
    ∀ᶠ M : ℕ in atTop, ∀ A D : ℕ,
      x < (A : ℝ)/(M : ℝ) → y < (D : ℝ)/(M : ℝ) → T ≤ A ∧ T ≤ D := by
  have hn : Tendsto (fun M : ℕ => (M : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hxm := (hn.const_mul_atTop hx).eventually_gt_atTop (T : ℝ)
  have hym := (hn.const_mul_atTop hy).eventually_gt_atTop (T : ℝ)
  filter_upwards [hxm,hym,eventually_gt_atTop (0:ℕ)] with M hMx hMy hM
  intro A D hA hD
  have hm : (0:ℝ) < M := Nat.cast_pos.mpr hM
  have hA' := (lt_div_iff₀ hm).mp hA
  have hD' := (lt_div_iff₀ hm).mp hD
  constructor
  · exact_mod_cast (show (T : ℝ) ≤ A by nlinarith)
  · exact_mod_cast (show (T : ℝ) ≤ D by nlinarith)

theorem exists_eventual_typical_finiteMenuError (a h ρ z ξ L U : ℝ)
    (ha : 0 < a) (hz0 : 0 ≤ z) (hz1 : z < 1) (hξ : 0 < ξ) (hξ1 : ξ < 1) (_hL : 0 < L)
    (hU : 0 < U) (hlower : h/2 < ρ) (hupper : ρ < a+h/2)
    (hq0 : 0 < sourceExposure a h ρ z) (hq1 : sourceExposure a h ρ z < 1)
    (hboxlo : (1-ξ)*U < (1-ξ*sourceExposure a h ρ z)*L)
    (hboxhi : (1-ξ*sourceExposure a h ρ z)*U < L)
    (c : ℕ → ℕ) (hc : Tendsto (fun M => (c M : ℝ)/(M : ℝ)) atTop (𝓝 ρ))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ M : ℕ in atTop, ∀ A H₀ H₁ : ℕ,
      |(A : ℝ)-(M : ℝ)*a| ≤ M*δ →
      |(H₀ : ℝ)-(M : ℝ)*(h/2)| ≤ M*δ →
      |(H₁ : ℝ)-(M : ℝ)*(h/2)| ≤ M*δ →
      let d₀ := activeResidual (c M) A H₀
      let d₁ := activeResidual (c M) A H₁
      let small := min d₀ d₁
      let ell := exclusiveQuota z A
      let gap := residualDifference d₀ d₁
      let K := 2*ell+gap
      let r := small-ell
      NormalizedGuardRegion ξ L U (finiteCountPoint M A small ell gap) ∧
      0 < A ∧ ell < small ∧ K < A ∧
      finiteHarmonicError ξ L U (1-ξ*sourceExposure a h ρ z) A K r+
        1/(A : ℝ)+|(K : ℝ)/(A : ℝ)-z| < ε := by
  let τ := ε/(U+U^2+3)
  have hden : 0 < U+U^2+3 := by positivity
  have hτ : 0 < τ := div_pos hε hden
  have hτeq : τ*(U+U^2+3)=ε := by dsimp [τ]; field_simp
  have hs := source_menu_neighborhood a h ρ z ξ L U τ ha hz1 hξ hξ1 hq0 hq1 hboxlo hboxhi hτ
  obtain ⟨δ,hδ,hcounts⟩ := eventually_typical_count_point_mem a h ρ z hz0 hz1.le
    hlower hupper c hc _ hs
  have hsam : ∀ᶠ D : ℕ in atTop, reciprocalSamplingError L D < τ :=
    (reciprocalSamplingError_tendsto_zero L).eventually (Iio_mem_nhds hτ)
  have hinv : ∀ᶠ A : ℕ in atTop, 1/(A : ℝ) < τ :=
    (tendsto_const_div_atTop_nhds_zero_nat (1:ℝ)).eventually (Iio_mem_nhds hτ)
  obtain ⟨T,hT⟩ := eventually_atTop.mp (hsam.and hinv)
  have hlarge := eventually_linear_counts_large (half_pos ha)
    (half_pos (mul_pos ha (sub_pos.mpr hz1))) T
  refine ⟨δ,hδ,?_⟩
  filter_upwards [hcounts,hlarge,eventually_gt_atTop (0:ℕ)] with M hMc hMl hM
  intro A H₀ H₁ hA hH₀ hH₁
  let d₀ := activeResidual (c M) A H₀
  let d₁ := activeResidual (c M) A H₁
  let small := min d₀ d₁
  let ell := exclusiveQuota z A
  let gap := residualDifference d₀ d₁
  let K := 2*ell+gap
  let r := small-ell
  let p := finiteCountPoint M A small ell gap
  have hp := hMc A H₀ H₁ hA hH₀ hH₁
  change NormalizedGuardRegion ξ L U p ∧ a/2 < p 0 ∧
    a*(1-z)/2 < normalizedMixed p ∧ |normalizedOwnerShare p-z| < τ ∧
    |normalizedFactor ξ p-(1-ξ*sourceExposure a h ρ z)| < τ at hp
  obtain ⟨hsmall,hK⟩ := count_region_integer_tests M A small ell gap hM hp.1
  have hApos : 0 < A := by omega
  have hDM : normalizedMixed p=((A-K : ℕ) : ℝ)/(M : ℝ) := by
    dsimp [normalizedMixed,p,finiteCountPoint,K]
    rw [Nat.cast_sub hK.le]
    push_cast
    ring
  have hg : normalizedFactor ξ p=finiteReceiptFactor ξ (A-K) r :=
    normalizedFactor_count_eq M A small ell gap hM hsmall hK
  have hshare : normalizedOwnerShare p=(K : ℝ)/(A : ℝ) :=
    normalizedOwnerShare_count_eq M A small ell gap hM hApos
  have ht := hMl A (A-K) hp.2.1 (by rw [←hDM]; exact hp.2.2.1)
  have hsample := (hT (A-K) ht.2).1
  have hAi := (hT A ht.1).2
  have hfactor : |finiteReceiptFactor ξ (A-K) r-(1-ξ*sourceExposure a h ρ z)| < τ := by
    rw [←hg]; exact hp.2.2.2.2
  have howner : |(K : ℝ)/(A : ℝ)-z| < τ := by rw [←hshare]; exact hp.2.2.2.1
  refine ⟨hp.1,hApos,hsmall,hK,?_⟩
  change U*|finiteReceiptFactor ξ (A-K) r-(1-ξ*sourceExposure a h ρ z)|+
    U^2*reciprocalSamplingError L (A-K)+1/(A : ℝ)+|(K : ℝ)/(A : ℝ)-z| < ε
  have hfirst := mul_lt_mul_of_pos_left hfactor hU
  have hsecond := mul_lt_mul_of_pos_left hsample (sq_pos_of_pos hU)
  nlinarith

end FCAppendix.Affine.Hybrid
