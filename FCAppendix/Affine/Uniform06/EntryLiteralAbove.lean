import FCAppendix.Affine.Uniform06.EntryLiteralCanonicalTransfer
import FCAppendix.Affine.Uniform06.EntryRawAbove
import FCAppendix.Affine.Uniform06.EntryRawModerate

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.EntryLiteralAbove

open MeasureTheory ProbabilityTheory Set Filter Topology LowBody
open FCAppendix.Affine.Uniform07 FCAppendix.Affine.WeightedSampling
open EntryEarlySourceLimits EntryRawCentral EntryRawGoodMoments EntryRawAbove
open EntryLiteralResponseGeometry EntryLiteralResponseMoments EntryLiteralCanonicalTransfer
open EntryResponseTransfer EntryReciprocalLimit LiteralExperiment
open scoped BigOperators
attribute [local instance] Classical.propDecidable

section Elementary
variable {Ξ : Type*} [MeasurableSpace Ξ] (P : Measure Ξ) [IsProbabilityMeasure P]

theorem mask_unit_error {Z : Ξ → ℝ} (hZ : MemLp Z 2 P)
    {S E : Set Ξ} (hS : MeasurableSet S) (hE : MeasurableSet E)
    (hSE : ∀ᵐ x ∂P,x∈S ↔ x∈E) :
    (∫ x, (S.indicator Z x-1)^2 ∂P) ≤
      (∫ x, (Z x-1)^2 ∂P)+P.real Eᶜ := by
  have hi := (integrable_const (1:ℝ) : Integrable (fun _ : Ξ => (1:ℝ)) P).indicator hE.compl
  have hzsq : Integrable (fun x => (Z x-1)^2) P :=
    (hZ.sub (memLp_const (1:ℝ))).integrable_sq
  have hsum := hzsq.add hi
  have hh := integral_mono_ae
    (((hZ.indicator hS).sub (memLp_const (1:ℝ))).integrable_sq) hsum (by
      filter_upwards [hSE] with x hx
      change (S.indicator Z x-1)^2 ≤ (Z x-1)^2+Eᶜ.indicator (fun _ => (1:ℝ)) x
      by_cases hs : x∈S
      · have he := hx.mp hs
        have hne : x∉Eᶜ := by simpa only [mem_compl_iff,not_not] using he
        rw [indicator_of_mem hs,indicator_of_notMem hne,add_zero]
      · have he : x∉E := fun he => hs (hx.mpr he)
        simp only [indicator_of_notMem hs,zero_sub,neg_sq,one_pow,
          indicator_of_mem (show x∈Eᶜ from he)]
        linarith [sq_nonneg (Z x-1)])
  simp only [Pi.add_apply,Pi.sub_apply] at hh
  rw [integral_add hzsq hi,integral_indicator_const (1:ℝ) hE.compl] at hh
  simp only [smul_eq_mul,mul_one] at hh
  exact hh

lemma product_unit_error_bound {a c Z A : ℝ} (_hc : 0 < c)
    (ha : |a| ≤ A) :
    (a*Z/c-1)^2 ≤ 2*(A/c)^2*(Z-1)^2+2*(a/c-1)^2 := by
  have hh : (a*Z/c-1)^2 ≤ 2*(a/c*(Z-1))^2+2*(a/c-1)^2 := by
    have he : a*Z/c-1=a/c*(Z-1)+(a/c-1) := by ring
    rw [he]
    nlinarith only [sq_nonneg (a/c*(Z-1)-(a/c-1))]
  have hsq : (a/c)^2 ≤ (A/c)^2 := by
    have hA : 0 ≤ A := (abs_nonneg a).trans ha
    have ha2 : a^2 ≤ A^2 := by nlinarith [sq_abs a,abs_nonneg a]
    simpa only [div_pow] using div_le_div_of_nonneg_right ha2 (sq_nonneg c)
  exact hh.trans (by
    simp only [mul_pow]
    nlinarith [mul_le_mul_of_nonneg_right hsq (sq_nonneg (Z-1))])

end Elementary

variable {N C : ℕ}

theorem response_coefficient_scale (ν : Measure RowRival) (i : Row) (g : GuardData)
    {b A U ε c q lo γ w s d R : ℝ} (h : Inputs ν i g N C b A U ε c q lo γ w s)
    (hd : 0 < d) (hdq : d ≤ q/(2*U)) (hR : 0 < R) (hstar : ℝ)
    (x : EntryIIDCentral.Row (Ω := RowRival) N) :
    ((N:ℝ)/R)*response ν i C g b A U ε x=
      coefficient N b d (slope ν i C g b A U ε x/(N:ℝ))*
        (if x∈usable ν i g b A U ε then
          max (deficit i C b g.multiplier c hstar x) 0/R else 0) := by
  have hh := response_coefficient_exact ν i g h hd hdq hstar x
  have hn : (0:ℝ)< N := by exact_mod_cast h.rivals_pos
  have hs := Real.sqrt_pos.mpr hn
  have ht := congrArg (fun z : ℝ => (Real.sqrt (N:ℝ)/R)*z) hh
  have hsq := Real.sq_sqrt hn.le
  convert! ht using 1
  · rw [← mul_assoc]
    congr 1
    field_simp [hR.ne']
    nlinarith [hsq]
  · by_cases hx : x∈usable ν i g b A U ε
    · simp only [normalizedGoodDeficit,if_pos hx]
      field_simp [hR.ne',hs.ne']
    · simp [normalizedGoodDeficit,hx]

section Original
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

theorem original_above_canonical_ratio
    (i : Row) (V : Ω → ℝ) (B : ℕ → Ω → ℝ)
    (hV : Measurable V) (hB : ∀ m, Measurable (B m))
    (hvalue : μ.map V=LowChernoff.conditionalValueLaw i)
    (hadmissible : ∀ m, ∀ᵐ ω ∂μ,B m ω ≤ V ω)
    (hactive : ∀ᵐ ω ∂μ,entry i < V ω → Tendsto (fun m => B m ω) atTop
      (𝓝 (ActiveGraphComponent.activeBid i (V ω))))
    (b : ℕ → ℝ) (_hbt : ∀ m,b m ≤ cutoff i) (hb : Tendsto b atTop (𝓝 (entry i)))
    (g : ℕ → GuardData) (_hl : Tendsto (fun m => (g m).multiplier) atTop (𝓝 (entry i)))
    (n : ℕ → ℕ) (_hnp : ∀ m,4 ≤ n m) (hn : Tendsto n atTop atTop)
    {ε q U lo : ℝ} (hε : 0 < ε) (hloLam : lo < entry i)
    (A γ w s : ℕ → ℝ)
    (hcap : ∀ m, ∀ᵐ p ∂joint μ V (B m),p.2 ≤ U)
    (hfinite : ∀ m, Inputs (RawMixedSource.source i (joint μ V (B m))) i (g m)
      (n m-1) (capacity (n m)) (b m) (A m) U ε (eligibleMass μ i V/2) q lo (γ m) (w m) (s m))
    (hδ : ∀ m,0 < EntryRawAbove.delta i (joint μ V (B m)) (n m-1) (capacity (n m)) (b m))
    (habove : Tendsto (fun m => EntryRawCentral.center i (joint μ V (B m)) (n m-1)
      (capacity (n m)) (b m)) atTop atTop) :
    let G := fun m => joint μ V (B m)
    let P := fun m => EntryIIDCentral.rowLaw (RawMixedSource.source i (G m)) (n m-1)
    let p : (m : ℕ) → EntryIIDCentral.Row (Ω := RowRival) (n m-1) → ℝ := fun m => response (RawMixedSource.source i (G m)) i
      (capacity (n m)) (g m) (b m) (A m) U ε
    let p0 := fun m => (P m).real {x | 0 < p m x}
    let Q := fun m => canonicalGoodMarginal i (G m) (capacity (n m)) (n m-1) (g m) (b m) (A m) U ε
    let R2 := fun m => canonicalGoodDuplicate i (G m) (capacity (n m)) (n m-1) (g m) (b m) (A m) U ε
    Tendsto p0 atTop (𝓝 1) ∧
      (∀ᶠ m in atTop,0 < p0 m ∧ 0 < Q m ∧ 0 < R2 m) ∧
      Tendsto (fun m => (Q m)^2/(p0 m*R2 m)) atTop (𝓝 1) ∧
      Tendsto (fun m => Q m/p0 m) atTop (𝓝 0) ∧
      Tendsto (fun m => (((n m-1:ℕ):ℝ)/
        (EntryRawAbove.delta i (G m) (n m-1) (capacity (n m)) (b m)*
          (1/(entry i*reciprocalMean μ i V))))*Q m) atTop (𝓝 1) := by
  let G := fun m => joint μ V (B m)
  letI (m : ℕ) : IsProbabilityMeasure (G m) :=
    Measure.isProbabilityMeasure_map (hV.prodMk (hB m)).aemeasurable
  let N := fun m => n m-1
  let C := fun m => capacity (n m)
  let ν := fun m => RawMixedSource.source i (G m)
  let P := fun m => EntryIIDCentral.rowLaw (ν m) (N m)
  let δ := fun m => EntryRawAbove.delta i (G m) (N m) (C m) (b m)
  have hδp (m : ℕ) : 0 < δ m := hδ m
  let D : (m : ℕ) → EntryIIDCentral.Row (Ω := RowRival) (N m) → ℝ := fun m => deficit i (C m) (b m) (g m).multiplier
    (eligibleMass μ i V/2) (eligibleHMean μ i V)
  let Zraw := fun m x => max (D m x) 0/δ m
  let E := fun m => goodEvent i (G m) (g m) (N m) ε (A m) U
  let S : (m : ℕ) → Set (EntryIIDCentral.Row (Ω := RowRival) (N m)) := fun m => usable (ν m) i (g m) (b m) (A m) U ε
  let Z := fun m => (S m).indicator (Zraw m)
  let p : (m : ℕ) → EntryIIDCentral.Row (Ω := RowRival) (N m) → ℝ := fun m => response (ν m) i (C m) (g m) (b m) (A m) U ε
  let Λ : (m : ℕ) → EntryIIDCentral.Row (Ω := RowRival) (N m) → ℝ := fun m => price (ν m) i (C m) (g m) (b m) (A m) U ε
  let K : (m : ℕ) → EntryIIDCentral.Row (Ω := RowRival) (N m) → ℝ := fun m => slope (ν m) i (C m) (g m) (b m) (A m) U ε
  let κ := reciprocalMean μ i V
  let d := min (q/(2*U)) (κ/2)
  let a0 := 1/(entry i*κ)
  let a := fun m x => coefficient (N m) (b m) d (K m x/(N m:ℝ))
  let Y := fun m x => ((N m:ℝ)/(δ m*a0))*p m x
  have hN : Tendsto N atTop atTop := PhysicalRates.rivals_tendsto.comp hn
  have hNp (m) : 0 < N m := (hfinite m).rivals_pos
  have hNr (m) : (0:ℝ)< N m := by exact_mod_cast hNp m
  have hlo : 0 < lo := (hfinite 0).lo_pos
  have hU : 0 < U := (hfinite 0).cap_pos
  have hq : 0 < q := (hfinite 0).strip_pos
  have hLam := EarlyMean.entry_pos i
  have hκ : 0 < κ := reciprocalMean_positive μ i V hV hvalue
  have hd : 0 < d := lt_min (div_pos hq (by positivity)) (by positivity)
  have hdq : d ≤ q/(2*U) := min_le_left _ _
  have hdκ : d ≤ κ := (min_le_right _ _).trans (by linarith)
  have ha0 : 0 < a0 := one_div_pos.mpr (mul_pos hLam hκ)
  have hblo (m) : lo ≤ b m := (hfinite m).lower_price.trans (hfinite m).bid_window.1
  have hbp (m) : 0 < b m := hlo.trans_le (hblo m)
  have hhstar : eligibleHMean μ i V ∈ Icc (0:ℝ) (1/2) :=
    ⟨(eligibleHMean_positive μ i V hV hvalue).le,(eligibleHMean_bounds μ i V hV hvalue).2⟩
  have hraw := raw_above_moments i G N C hNp b (fun m => (g m).multiplier) hbp
    (eligibleMass μ i V/2) (eligibleHMean μ i V) hhstar hδ habove
  have hZmraw (m) : Measurable (Zraw m) :=
    ((measurable_deficit i (N m) (C m) (b m) (g m).multiplier
      (eligibleMass μ i V/2) (eligibleHMean μ i V)).max measurable_const).div_const _
  have hZraw (m) : MemLp (Zraw m) 2 (P m) := by
    apply MemLp.of_bound (hZmraw m).aestronglyMeasurable ((C m:ℝ)/δ m)
    exact ae_of_all _ fun x => by
      rw [Real.norm_eq_abs,abs_of_nonneg (div_nonneg (le_max_right _ _) (hδp m).le)]
      exact div_le_div_of_nonneg_right
        (max_le (deficit_le_capacity i (C m) (hbp m) (g m).multiplier
          (eligibleMass μ i V/2) hhstar.1 x) (Nat.cast_nonneg _)) (hδp m).le
  have hSm (m) : MeasurableSet (S m) := measurable_usable _ i _ _ _ _ _
  have hEm (m) : MeasurableSet (E m) := measurable_goodEvent i (G m) (g m) (N m) ε (A m) U
  have hZ (m) : MemLp (Z m) 2 (P m) := (hZraw m).indicator (hSm m)
  have hZm (m) : Measurable (Z m) := (hZmraw m).indicator (hSm m)
  have hrawerr : Tendsto (fun m => ∫ x, (Zraw m x-1)^2 ∂P m) atTop (𝓝 0) := by
    have hinv := (tendsto_inv_atTop_zero.comp habove).pow 2
    have hrhs : Tendsto (fun m => 4*(N m:ℝ)/(δ m)^2) atTop (𝓝 0) := by
      have he (m) : 4*(N m:ℝ)/(δ m)^2=4*(EntryRawCentral.center i (G m) (N m) (C m) (b m))⁻¹^2 := by
        simp only [EntryRawCentral.center,EntryRawAbove.delta,δ,inv_div,div_pow,Real.sq_sqrt (Nat.cast_nonneg _)]
        ring
      simp_rw [he]
      simpa using hinv.const_mul 4
    exact squeeze_zero (fun _ => integral_nonneg fun _ => sq_nonneg _)
      (fun m => raw_normalized_deficit_error i (G m) (N m) (C m) (hbp m) (g m).multiplier
        (eligibleMass μ i V/2) hhstar (hδp m)) hrhs
  have hbad : Tendsto (fun m => (P m).real (E m)ᶜ) atTop (𝓝 0) := by
    have harg : Tendsto (fun m => 2*(N m:ℝ)*ε^2) atTop atTop := by
      have ht := (tendsto_natCast_atTop_atTop.comp hN).const_mul_atTop
        (by positivity : 0 < 2*ε^2)
      convert! ht using 1
      funext m
      dsimp only [Function.comp_def]
      ring
    have he : Tendsto (fun m => Real.exp (-(2*(N m:ℝ)*ε^2))) atTop (𝓝 (0:ℝ)) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp harg
    have hr : Tendsto (fun m => 18*Real.exp (-2*(N m:ℝ)*ε^2)) atTop (𝓝 0) := by
      simpa only [neg_mul,mul_zero] using he.const_mul (18:ℝ)
    apply squeeze_zero (fun _ => measureReal_nonneg) (fun m => ?_) hr
    exact goodEvent_complement_le i (G m) (g m) (N m) (hNp m)
      (hfinite m).prefix.lower_pos (by linarith [(hfinite m).prefix.lower_pos,(hfinite m).radius_pos])
      (hfinite m).prefix.rejectionScale_pos hε.le (A m) U
  have hZerr : Tendsto (fun m => ∫ x, (Z m x-1)^2 ∂P m) atTop (𝓝 0) :=
    squeeze_zero (fun _ => integral_nonneg fun _ => sq_nonneg _)
      (fun m => mask_unit_error (P m) (hZraw m) (hSm m) (hEm m)
        ((usable_ae_good (N := N m) i (G m) (g m) (b m) (A m) U ε (hcap m)).mono
          fun _ hx => Iff.of_eq hx))
      (by simpa using hrawerr.add hbad)
  have hdeltaN : Tendsto (fun m => δ m/(N m:ℝ)) atTop (𝓝 0) := by
    have hh := (PhysicalRates.rival_capacity_density_tendsto.comp hn).sub
      (EntryRawModerate.raw_mean_tendsto μ i V B hV hB hvalue hadmissible hactive b hbp hb)
    simp only [sub_self] at hh
    apply hh.congr
    intro m
    change (C m:ℝ)/(N m:ℝ)-RawMixedSource.mean i (G m) (b m)=δ m/(N m:ℝ)
    dsimp only [δ,EntryRawAbove.delta]
    field_simp [(hNr m).ne']
  have hDN : Tendsto (fun m => ∫ x, max (D m x) 0/(N m:ℝ) ∂P m) atTop (𝓝 0) := by
    have hh := hraw.1.mul hdeltaN
    simp only [one_mul] at hh
    apply hh.congr
    intro m
    rw [← integral_mul_const]
    apply integral_congr_ae
    exact ae_of_all _ fun x => by
      change (max (D m x) 0/δ m)*(δ m/(N m:ℝ))=max (D m x) 0/(N m:ℝ)
      field_simp [(hδp m).ne']
  have hgeom (m) (x) := total_finite_geometry (ν m) i (g m) (hfinite m) (eligibleHMean μ i V) x
  have hLm (m) : Measurable (Λ m) := measurable_price _ i _ _ _ _ _ _
  have hKm (m) : Measurable (K m) := measurable_slope _ i _ _ _ _ _ _
  have hmove : Tendsto (fun m => ∫ x, b m-Λ m x ∂P m) atTop (𝓝 0) := by
    have hscale : 0 ≤ xi i/(q/(2*U)) := by have := xi_pos i; positivity
    apply squeeze_zero (fun m => integral_nonneg fun x => (finite_displacement _ i (g m)
      (hfinite m) (eligibleHMean μ i V) x).1) (fun m => ?_) (by simpa using hDN.const_mul (xi i/(q/(2*U))))
    have hiL : Integrable (fun x => b m-Λ m x) (P m) := Integrable.of_mem_Icc 0 (b m-lo)
      (measurable_const.sub (hLm m)).aemeasurable (ae_of_all _ fun x =>
        ⟨by linarith [(hgeom m x).2.1],by linarith [(hgeom m x).1]⟩)
    have hiD : Integrable (fun x => max (D m x) 0/(N m:ℝ)) (P m) := by
      have hz := ((hZraw m).integrable (by norm_num)).const_mul (δ m/(N m:ℝ))
      apply hz.congr
      exact ae_of_all _ fun x => by dsimp only [Zraw]; field_simp [(hδp m).ne']
    have hh := integral_mono hiL (hiD.const_mul (xi i/(q/(2*U))))
      (fun x => by simpa only [mul_div_assoc] using
        (finite_displacement _ i (g m) (hfinite m) (eligibleHMean μ i V) x).2)
    simpa only [integral_const_mul] using hh
  have hKlim := EntryRandomReciprocal.actual_random_reciprocal_L1 μ i V B hV hB hvalue
    hadmissible hactive hlo hloLam b hblo hb N hNp hN
    (fun m => profile i (g m) (b m)) (fun m => measurable_profile i (g m) (b m))
    Λ K hLm hKm (fun m x => ⟨(hgeom m x).1,(hgeom m x).2.1⟩)
    (fun m x => ⟨(hgeom m x).2.2.1,(hgeom m x).2.2.2.1⟩) hmove
  have hKi (m) : Integrable (fun x => |K m x/(N m:ℝ)-κ|) (P m) := by
    apply Integrable.of_bound (((hKm m).div_const _).sub_const κ).abs.aestronglyMeasurable (2/lo+|κ|)
    exact ae_of_all _ fun x => by
      rw [Real.norm_eq_abs,abs_abs]
      have hh := slope_normalized_bounds _ i (g m) (hfinite m) (eligibleHMean μ i V) x
      calc
        |K m x/(N m:ℝ)-κ| ≤ |K m x/(N m:ℝ)|+|κ| := abs_sub _ _
        _ ≤ 2/lo+|κ| := add_le_add (by
          rw [abs_of_nonneg (show 0 ≤ K m x/(N m:ℝ) from hh.1)]
          exact hh.2) le_rfl
  have haLim := coefficient_L1 P N hN b hlo hLam hblo hb hd hκ hdκ
    (fun m x => K m x/(N m:ℝ)) (fun m => (hKm m).div_const _) hKi hKlim
  have ham (m) : Measurable (a m) := by dsimp [a,coefficient]; fun_prop
  have hab (m) (x) : |a m x| ≤ 1/(lo*d) := by
    have hh := coefficient_bounds hlo (hblo m) hd (N := N m) (k := K m x/(N m:ℝ))
    rw [abs_of_pos hh.1]
    exact hh.2
  have hpbound (m) (x) : p m x ∈ Icc (0:ℝ) 1 := by
    dsimp [p,response]
    split_ifs
    · exact EntryLiteralResponseGeometry.complement_bounds i (C m) (g m) (b m) x
    · norm_num
  have hYid (m) (x) : Y m x=a m x*Z m x/a0 := by
    have hh := response_coefficient_scale (ν m) i (g m) (hfinite m) hd hdq (hδp m)
      (eligibleHMean μ i V) x
    change ((N m:ℝ)/δ m)*p m x=a m x*Z m x at hh
    dsimp only [Y]
    rw [show ((N m:ℝ)/(δ m*a0))*p m x=(((N m:ℝ)/δ m)*p m x)/a0 by ring,hh]
  have hYm (m) : Measurable (Y m) := (measurable_response _ i _ _ _ _ _ _).const_mul _
  have hYlp (m) : MemLp (Y m) 2 (P m) := by
    apply MemLp.of_bound (hYm m).aestronglyMeasurable ((N m:ℝ)/(δ m*a0))
    exact ae_of_all _ fun x => by
      rw [Real.norm_eq_abs,abs_mul,abs_of_pos (div_pos (hNr m) (mul_pos (hδp m) ha0)),
        abs_of_nonneg (hpbound m x).1]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (hpbound m x).2
        (div_pos (hNr m) (mul_pos (hδp m) ha0)).le
  have hYzero (m) : ∀ᵐ x ∂P m,0 ≤ Y m x :=
    ae_of_all _ fun x => mul_nonneg
      (div_pos (hNr m) (mul_pos (hδp m) ha0)).le (hpbound m x).1
  have hYerr : Tendsto (fun m => ∫ x, (Y m x-1)^2 ∂P m) atTop (𝓝 0) := by
    let L := (1/(lo*d))/a0
    let e := fun m x => a m x/a0-1
    have hL : 0 ≤ L := by dsimp [L]; positivity
    have hem (m) : Measurable (e m) := ((ham m).div_const a0).sub_const 1
    have heb (m) (x) : |e m x| ≤ L+1 := by
      dsimp [e]
      exact (abs_sub _ _).trans (by
        rw [abs_div,abs_of_pos ha0,abs_one]
        have ht := div_le_div_of_nonneg_right (hab m x) ha0.le
        change |a m x| / a0+1 ≤ (1/(lo*d))/a0+1
        linarith)
    have hei (m) : Integrable (fun x => |e m x|) (P m) :=
      Integrable.of_bound (hem m).abs.aestronglyMeasurable (L+1)
        (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs,abs_abs] using heb m x)
    have heL1 : Tendsto (fun m => ∫ x, |e m x| ∂P m) atTop (𝓝 0) := by
      have hh := haLim.div_const a0
      simp only [zero_div] at hh
      apply hh.congr
      intro m
      rw [← integral_div]
      apply integral_congr_ae
      exact ae_of_all _ fun x => by
        dsimp [e]
        rw [show a m x/a0-1=(a m x-a0)/a0 by field_simp [ha0.ne'],abs_div,abs_of_pos ha0]
    have hbound (m) (x) : (Y m x-1)^2 ≤
        2*L^2*(Z m x-1)^2+2*(L+1)*|e m x| := by
      rw [hYid]
      have hp := product_unit_error_bound (Z := Z m x) ha0 (hab m x)
      have he2 : (e m x)^2 ≤ (L+1)*|e m x| := by
        nlinarith [mul_le_mul_of_nonneg_right (heb m x) (abs_nonneg (e m x)),sq_abs (e m x)]
      exact hp.trans (by dsimp only [L,e] at *; linarith)
    apply squeeze_zero (fun _ => integral_nonneg fun _ => sq_nonneg _)
      (fun m => ?_) (by simpa using (hZerr.const_mul (2*L^2)).add (heL1.const_mul (2*(L+1))))
    have hi := (((hZ m).sub (memLp_const (1:ℝ))).integrable_sq.const_mul (2*L^2)).add
      ((hei m).const_mul (2*(L+1)))
    have hI1 : Integrable (fun x => 2*L^2*(Z m x-1)^2) (P m) :=
      ((hZ m).sub (memLp_const (1:ℝ))).integrable_sq.const_mul (2*L^2)
    have hI2 : Integrable (fun x => 2*(L+1)*|e m x|) (P m) :=
      (hei m).const_mul (2*(L+1))
    have hh := integral_mono (((hYlp m).sub (memLp_const (1:ℝ))).integrable_sq) hi (hbound m)
    change (∫ x,(Y m x-1)^2 ∂P m) ≤
      ∫ x,2*L^2*(Z m x-1)^2+2*(L+1)*|e m x| ∂P m at hh
    rw [integral_add hI1 hI2,integral_const_mul,integral_const_mul] at hh
    exact hh
  have hout := AboveEntry.ratio_tendsto_one_of_L2 P Y hYm hYlp hYzero hYerr
  have hpEq (m) : {x | 0< Y m x}={x | 0< p m x} := by
    ext x
    exact mul_pos_iff_of_pos_left (div_pos (hNr m) (mul_pos (hδp m) ha0))
  have hQEq (m) : (∫ x, Y m x ∂P m)=((N m:ℝ)/(δ m*a0))*
      canonicalGoodMarginal i (G m) (C m) (N m) (g m) (b m) (A m) U ε := by
    dsimp only [Y]
    rw [integral_const_mul,(integrated_canonical_moments i (G m) (g m) (hfinite m) (hcap m)).1]
  have hREq (m) : (∫ x, (Y m x)^2 ∂P m)=((N m:ℝ)/(δ m*a0))^2*
      canonicalGoodDuplicate i (G m) (C m) (N m) (g m) (b m) (A m) U ε := by
    simp only [Y,mul_pow,integral_const_mul]
    rw [(integrated_canonical_moments i (G m) (g m) (hfinite m) (hcap m)).2]
  have hp0 := hout.2.1
  simp_rw [hpEq] at hp0
  have hQzero : Tendsto (fun m => canonicalGoodMarginal i (G m) (C m) (N m)
      (g m) (b m) (A m) U ε) atTop (𝓝 0) := by
    have hh := (hdeltaN.mul_const a0).mul hout.1
    simp only [zero_mul] at hh
    apply hh.congr
    intro m
    rw [hQEq]
    field_simp [(hNr m).ne',(hδp m).ne',ha0.ne']
  have hconditional : Tendsto (fun m => canonicalGoodMarginal i (G m) (C m) (N m)
      (g m) (b m) (A m) U ε/(P m).real {x | 0 < p m x}) atTop (𝓝 0) := by
    have ht := hQzero.div hp0 (by norm_num : (1:ℝ)≠0)
    simp only [zero_div] at ht
    apply ht.congr
    intro m
    rfl
  refine ⟨hp0,?_,?_,hconditional,?_⟩
  · filter_upwards [hp0.eventually_const_lt (by norm_num : (0:ℝ)<1),
      hout.1.eventually_const_lt (by norm_num : (0:ℝ)<1),
      hout.2.2.1.eventually_const_lt (by norm_num : (0:ℝ)<1)] with m hm hQ hR
    rw [hQEq] at hQ
    rw [hREq] at hR
    exact ⟨hm,pos_of_mul_pos_right hQ (div_pos (hNr m) (mul_pos (hδp m) ha0)).le,
      pos_of_mul_pos_right hR (sq_nonneg _)⟩
  · apply hout.2.2.2.congr
    intro m
    rw [hQEq,hREq,hpEq]
    exact normalized_ratio_eq (div_ne_zero (hNr m).ne' (mul_ne_zero (hδp m).ne' ha0.ne'))
  · simpa only [hQEq] using hout.1

end Original
end FCAppendix.Affine.Uniform06.EntryLiteralAbove
