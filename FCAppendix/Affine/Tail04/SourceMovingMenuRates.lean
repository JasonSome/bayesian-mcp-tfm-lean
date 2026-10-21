import FCAppendix.Affine.Tail04.SourceMovingScalarGuards
import FCAppendix.Affine.Tail04.SourceTailNoisyGap
import FCAppendix.Affine.Tail04.OriginalNoisySequence

noncomputable section
namespace FCAppendix.Affine.Tail04.SourceMovingMenuRates
open MeasureTheory ProbabilityTheory Set Filter Topology Classical
open OriginalValues SourceMovingScalarGuards SourceTailTaylor SourceTailCapGap
open OriginalNoisySequence

theorem cutoff_square_over_sqrt :
    Tendsto (fun N : ℕ=> cutoff N^2/Real.sqrt (N:ℝ)) atTop (𝓝 0) := by
  have hsame : Tendsto (fun N : ℕ=> cutoff N^2/Real.sqrt (N+1:ℕ)) atTop (𝓝 0) := by
    have hh := allocation_error_ratio_tendsto.comp (tendsto_add_atTop_nat 1)
    apply hh.congr'
    filter_upwards [eventually_ge_atTop (1:ℕ)] with N hN
    have ht := movingThreshold_pos (N+1) (by omega)
    dsimp only [Function.comp_def,cutoff]
    field_simp [ht.ne']
  apply squeeze_zero' (Eventually.of_forall (fun N=> by positivity)) _ (by simpa only [mul_zero] using! hsame.const_mul 2)
  filter_upwards [eventually_ge_atTop (1:ℕ)] with N hN
  have hn : (1:ℝ)≤ N := by exact_mod_cast hN
  have hN0 : (0:ℝ)< N := by linarith
  have hs : Real.sqrt (N+1:ℕ)≤2*Real.sqrt (N:ℝ) := by
    have h0 := Real.sqrt_nonneg (N:ℝ)
    have h1 := Real.sqrt_nonneg (N+1:ℕ)
    have h0' := Real.sq_sqrt (Nat.cast_nonneg N)
    have h1' := Real.sq_sqrt (Nat.cast_nonneg (N+1))
    push_cast at h1' h1 ⊢
    nlinarith
  have hs0 : 0< Real.sqrt (N:ℝ) := Real.sqrt_pos.mpr hN0
  have hs1 : 0< Real.sqrt (N+1:ℕ) := Real.sqrt_pos.mpr (by positivity)
  rw [←mul_div_assoc]
  apply (div_le_div_iff₀ hs0 hs1).mpr
  have hh := mul_le_mul_of_nonneg_left hs (sq_nonneg (cutoff N))
  nlinarith only [hh]

theorem cutoff_square_over_rivals :
    Tendsto (fun N : ℕ=> cutoff N^2/(N:ℝ)) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun N=> by positivity)) _ cutoff_square_over_sqrt
  filter_upwards [eventually_ge_atTop (1:ℕ)] with N hN
  have hn : (1:ℝ)≤ N := by exact_mod_cast hN
  have hs := Real.sqrt_nonneg (N:ℝ)
  have hs' := Real.sq_sqrt (Nat.cast_nonneg N)
  have hsN : Real.sqrt (N:ℝ)≤ N := by nlinarith
  exact div_le_div_of_nonneg_left (sq_nonneg _) (Real.sqrt_pos.mpr (by linarith)) hsN

theorem cutoff_square_exponential {q : ℝ} (hq : 0< q) :
    Tendsto (fun N : ℕ=> cutoff N^2*Real.exp (-q*(N:ℝ))) atTop (𝓝 0) := by
  have hp : Tendsto (fun N : ℕ=>(N:ℝ)^2*Real.exp (-q*(N:ℝ))) atTop (𝓝 0) := by
    simpa only [Real.rpow_two,Function.comp_def] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (2:ℝ) q hq).comp
        tendsto_natCast_atTop_atTop
  apply squeeze_zero' (Eventually.of_forall (fun N=> by positivity)) _ (by simpa only [mul_zero] using! hp.const_mul 4)
  filter_upwards [eventually_ge_atTop (1:ℕ)] with N hN
  have hn : (1:ℝ)≤ N := by exact_mod_cast hN
  have ht := movingThreshold_le_population (N+1) (by omega)
  have ht0 := (movingThreshold_pos (N+1) (by omega)).le
  have hsq : cutoff N^2≤4*(N:ℝ)^2 := by
    change movingThreshold (N+1)^2≤4*(N:ℝ)^2
    push_cast at ht
    nlinarith
  have hh := mul_le_mul_of_nonneg_right hsq (Real.exp_nonneg (-q*(N:ℝ)))
  nlinarith only [hh]

def rate (K s w : ℝ) (N : ℕ) : ℝ :=
  K*(5/Real.sqrt (N:ℝ)+4/(N:ℝ))+
    75/(2*Real.sqrt (N:ℝ))+
    2*Real.exp (-(N:ℝ)*s^2/2)+
    4*(2/(w*(N:ℝ))+Real.exp (-(N:ℝ)*w^2/2))

lemma rate_nonneg {K s w : ℝ} (hK : 0≤ K) (hw : 0≤ w) (N : ℕ) :
    0≤ rate K s w N := by unfold rate;positivity

theorem scaled_rate_tendsto {K s w : ℝ} (hs : 0< s) (hw : 0< w) :
    Tendsto (fun N=> cutoff N^2*rate K s w N) atTop (𝓝 0) := by
  have hs' : 0< s^2/2 := by positivity
  have hw' : 0< w^2/2 := by positivity
  have h1 := cutoff_square_over_sqrt
  have h2 := cutoff_square_over_rivals
  have h3 := cutoff_square_exponential hs'
  have h4 := cutoff_square_exponential hw'
  have hh := ((((h1.const_mul 5).add (h2.const_mul 4)).const_mul K).add
    (h1.const_mul (75/2))).add (h3.const_mul 2) |>.add
      (((h2.const_mul (2/w)).add h4).const_mul 4)
  convert! hh using 1
  · funext N
    dsimp only [rate]
    rw [show -(N:ℝ)*s^2/2=-(s^2/2)*(N:ℝ) by ring,
      show -(N:ℝ)*w^2/2=-(w^2/2)*(N:ℝ) by ring]
    field_simp
  · simp

theorem utility_rate_tendsto {K s w : ℝ} (hs : 0< s) (hw : 0< w)
    (hK : 0≤ K) {B : ℝ} (hB : 0≤ B) :
    Tendsto (fun N=>(cutoff N+2*B)*rate K s w N) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun N=> mul_nonneg
    (by have ht := (movingThreshold_pos (N+1) (by omega)).le;change 0≤ movingThreshold (N+1)+2*B;linarith)
      (rate_nonneg (s:=s) hK hw.le N))) _
    (by simpa only [mul_zero] using! (scaled_rate_tendsto (K:=K) hs hw).const_mul (1+2*B))
  filter_upwards [Eventually.of_forall (fun N=> movingThreshold_ge_one (N+1) (by omega))]
    with N ht
  have hfac : cutoff N+2*B≤(1+2*B)*cutoff N^2 := by
    change 1≤ cutoff N at ht
    nlinarith [mul_nonneg hB (show 0≤ cutoff N^2-1 by nlinarith)]
  have hh := mul_le_mul_of_nonneg_right hfac (rate_nonneg (s:=s) hK hw.le N)
  nlinarith only [hh]

theorem eventually_tail_error {K s w B C : ℝ}
    (hs : 0< s) (hw : 0< w) (hK : 0≤ K) (hB : 0≤ B) (hC : 0< C) :
    ∀ᶠ N in atTop,2*(cutoff N+2*B)*rate K s w N< C/cutoff N := by
  have hh := ((scaled_rate_tendsto (K:=K) hs hw).const_mul (2*(1+2*B))).eventually
    (gt_mem_nhds (by simpa only [mul_zero] using! hC))
  filter_upwards [hh] with N hN
  have ht := movingThreshold_pos (N+1) (by omega)
  have ht1 := movingThreshold_ge_one (N+1) (by omega)
  change 0< cutoff N at ht
  change 1≤ cutoff N at ht1
  have hfac : cutoff N*(cutoff N+2*B)≤(1+2*B)*cutoff N^2 := by
    nlinarith [mul_nonneg hB (show 0≤ cutoff N^2-cutoff N by nlinarith)]
  apply (lt_div_iff₀ ht).mpr
  have hm := mul_le_mul_of_nonneg_right hfac (rate_nonneg (s:=s) hK hw.le N)
  nlinarith only [hm,hN]

theorem eventually_bulk_error {K s w B κ u : ℝ}
    (hs : 0< s) (hw : 0< w) (hK : 0≤ K) (hB : 0≤ B) (hκ : 0< κ) (hu : 0< u) :
    ∀ᶠ N in atTop,2*(cutoff N+2*B)*rate K s w N< κ*u/2 := by
  have hh := ((utility_rate_tendsto hs hw hK hB).const_mul 2).eventually
    (gt_mem_nhds (by simpa only [mul_zero] using! (show 0< κ*u/2 by positivity)))
  simpa only [mul_assoc] using hh

theorem eventually_tail_geometry {ξ Amin Amax k : ℝ}
    (hξ : 0< ξ) (hmin : 0< Amin) (hk : k<1/(2*Amax)) :
    ∀ᶠ N in atTop,
      endpointRadius Amin/cutoff N≤ Central.B ξ-1 ∧
      2*taylorConstant ξ (endpointRadius Amin)/cutoff N^2≤
        Amin*(stripWidth Amax k)^2/(4*cutoff N) := by
  have hB : 0< Central.B ξ-1 := by unfold Central.B;linarith
  have hd := stripWidth_pos hk
  have hright : 0< Amin*(stripWidth Amax k)^2/4 := by positivity
  have hleft : Tendsto (fun N=> endpointRadius Amin/cutoff N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop cutoff_tendsto
  have hTaylor : Tendsto (fun N=>2*taylorConstant ξ (endpointRadius Amin)/cutoff N)
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop cutoff_tendsto
  filter_upwards [hleft.eventually (gt_mem_nhds hB),hTaylor.eventually (gt_mem_nhds hright)]
    with N hL hT
  refine ⟨hL.le,?_⟩
  have ht := movingThreshold_pos (N+1) (by omega)
  change 0< cutoff N at ht
  have hh := div_le_div_of_nonneg_right hT.le ht.le
  convert! hh using 1 <;> field_simp [ht.ne']

theorem inwardCut_lt_cap {ξ Amax k : ℝ} (hk : k<1/(2*Amax)) (N : ℕ) :
    inwardCut (Central.B ξ) Amax k (cutoff N)< cap ξ k N := by
  have hd := div_pos (stripWidth_pos hk) (movingThreshold_pos (N+1) (by omega))
  dsimp only [inwardCut,cap,movingCap,cutoff] at *
  rw [add_div]
  linarith

theorem sequence_eventually_tail_noise
    (D : FiniteTailNoisyGame.Data) (P : ValueParameters) (t : ℝ) (ht : P.M< t)
    (N : ℕ) (S : Sequence D P t ht N) {Amax k : ℝ} (hk : k<1/(2*Amax)) :
    ∀ᶠ j in atTop,(S.data j).eps*(S.data j).U≤ stripWidth Amax k/(4*t) := by
  have hlim := S.noise_real_tendsto.mul_const D.U
  have hpos : 0< stripWidth Amax k/(4*t) :=
    div_pos (stripWidth_pos hk) (mul_pos (by norm_num) (P.M_pos.trans ht))
  have hh := hlim.eventually (gt_mem_nhds (by simpa only [zero_mul] using! hpos))
  exact hh.mono (fun j hj=> hj.le)

end FCAppendix.Affine.Tail04.SourceMovingMenuRates
