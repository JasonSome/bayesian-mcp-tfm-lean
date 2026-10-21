import FCAppendix.Affine.Hybrid.Finishing01Definitions
import FCAppendix.Affine.Hybrid.Finishing01MenusTransport

noncomputable section
namespace FCAppendix.Affine.Hybrid.Finishing01Menus
open MeasureTheory ProbabilityTheory Set Filter Topology Classical
open scoped BigOperators

variable (P : Finish01.Primitives)

lemma full_row_error_modulus_zero {δ δg δeq : ℝ}
    (hδ : 0<δ) (hδg : 0<δg) (hδeq : 0<δeq) :
    Tendsto (fun N : ℕ => 8*Real.exp (-(N:ℝ)*δ^2/2)+
      activeGuardExceptionError P.h δg δeq N) atTop (𝓝 0) := by
  have hn : Tendsto (fun N : ℕ => (N:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hx := Real.tendsto_exp_neg_atTop_nhds_zero.comp
    (hn.const_mul_atTop (by positivity : 0<δ^2/2))
  have he : Tendsto (fun N : ℕ => 8*Real.exp (-(N:ℝ)*δ^2/2)) atTop (𝓝 0) := by
    convert! hx.const_mul 8 using 1
    · funext N
      congr 2
      ring
    · ring
  simpa only [add_zero] using he.add
    (activeGuardExceptionError_tendsto_zero P.h_pos hδg hδeq)

theorem full_row_reference_limit (W : ℝ) (hLW : P.L≤ W)
    (hboxlo : P.kappa*W<P.h0*P.L) (hboxhi : P.h0*W<P.L)
    (c : ℕ→ℕ)
    (hc : Tendsto (fun M => (c M:ℝ)/(M:ℝ)) atTop (𝓝 P.rho))
    (V : ℝ) (hV : 0≤ V) (ε : ℝ) (hε : 0<ε) :
    ∀ᶠN in atTop,∀ T∈ Icc P.L W,
      ∀(F G : Measure ℝ) [IsProbabilityMeasure F] [IsProbabilityMeasure G],
      (∀ᵐb∂G,b∈ Icc P.L T) → ∀ v : ℝ, |v|≤ V → ∀ b∈ Icc P.L T,
      |actualRowInterim (N:=N) P.xi P.z P.L T (c (N+1)) P.categories F G v b-
        P.reference v (P.h0/reciprocalMean G) b|<ε := by
  have hW : 0<W := P.L_pos.trans_le hLW
  obtain ⟨δ,hδ,hmenus⟩ := exists_eventual_uniform_typical_menus
    P.a P.h P.rho P.z P.xi P.eta P.L W V
    P.a_pos P.z_nonneg P.z_lt_one P.xi_pos P.xi_lt_one
    P.L_pos hLW hV P.rho_lower P.rho_upper P.qbar_pos P.qbar_lt_one
    hboxlo hboxhi c hc (ε/2) (half_pos hε)
  obtain ⟨δg,δeq,hδg,_hδgs,hδeq,hguards⟩ :=
    exists_eventual_activePattern_guard_bound
      P.s P.a P.h P.rho P.z P.xi P.L W
      P.s_pos P.a_pos P.h_pos P.mass P.z_nonneg P.z_lt_one
      P.xi_pos P.xi_lt_one P.L_pos hLW P.rho_lower P.rho_upper
      P.qbar_pos P.qbar_lt_one hboxlo hboxhi c hc
  let C := (V+3*W)+(V+W+broadcastExposureModulus P.eta V W)+1
  have hmod : 0≤ broadcastExposureModulus P.eta V W :=
    broadcastExposureModulus_nonneg hV hW.le
  have hC : 0<C := by dsimp [C]; positivity
  have htail : ∀ᶠ N : ℕ in atTop,
      8*Real.exp (-(N:ℝ)*δ^2/2)+activeGuardExceptionError P.h δg δeq N<ε/(2*C) :=
    (full_row_error_modulus_zero P hδ hδg hδeq).eventually
      (gt_mem_nhds (by positivity))
  have hn : Tendsto (fun N : ℕ => (N:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hprefix : ∀ᶠN : ℕ in atTop, (1:ℝ)≤(N:ℝ)*δ/2 := by
    have ht : Tendsto (fun N : ℕ => (N:ℝ)*δ/2) atTop atTop := by
      convert! hn.const_mul_atTop (half_pos hδ) using 1
      funext N
      ring
    exact ht.eventually_ge_atTop 1
  have hmenusN := (tendsto_add_atTop_nat 1).eventually hmenus
  filter_upwards [hmenusN,hguards,hprefix,htail] with N hmenu hguard hpre hsmall
  intro T hT F G _ _ hG v hv b hb
  let E : (Fin N→ Fin 4)→ Prop := fun kind =>
    activePatternCountException P.categories δ kind ∨
      ¬activePatternGuarded P.xi P.L W (c (N+1)) P.z kind
  let R := P.reference v (P.h0/reciprocalMean G) b
  have hGW : ∀ᵐb∂G,b∈ Icc P.L W := by
    filter_upwards [hG] with b hb
    exact ⟨hb.1,hb.2.trans hT.2⟩
  have hbW : b∈ Icc P.L W := ⟨hb.1,hb.2.trans hT.2⟩
  have hbabs : |b|≤ W := by
    rw [abs_of_pos (P.L_pos.trans_le hb.1)]
    exact hbW.2
  have hq := exposure_mem_of_mean_factor G P.xi_pos P.xi_lt_one P.L_pos
    hGW hbW P.h0_pos.le hboxlo hboxhi
  have hR : |R|≤ V+W+broadcastExposureModulus P.eta V W := by
    have ha := (abs_sub v b).trans (add_le_add hv hbabs)
    have hb' := independentTwo_abs_le (eta:=P.eta) hv hbabs hq
    have hz : P.z≤1 := P.z_lt_one.le
    have he : 0≤1-P.z := by linarith
    dsimp [R,Finish01.Primitives.reference]
    apply (abs_add_le _ _).trans
    rw [abs_mul,abs_mul,abs_of_nonneg P.z_nonneg,abs_of_nonneg he]
    have hh := add_le_add (mul_le_mul_of_nonneg_left ha P.z_nonneg)
      (mul_le_mul_of_nonneg_left hb' he)
    apply hh.trans
    have ha0 : 0≤ V+W := by positivity
    nlinarith [mul_nonneg P.z_nonneg hmod,mul_nonneg he ha0]
  have hbad (kind : Fin N→ Fin 4) :
      |patternInterim P.xi P.z P.L T (c (N+1)) kind F G v b-R|≤ C := by
    have hh := abs_patternInterim_le P.xi_pos P.xi_lt_one P.L_pos
      P.z (c (N+1)) kind F G hG v b hb
    apply (abs_sub _ _).trans
    have hsum := add_le_add hh hR
    dsimp [C]
    exact hsum.trans (by linarith [hT.2])
  have hgood (kind : Fin N→ Fin 4) (he : ¬E kind) :
      |patternInterim P.xi P.z P.L T (c (N+1)) kind F G v b-R|≤ε/2 := by
    have hcount : ¬activePatternCountException P.categories δ kind :=
      fun h => he (Or.inl h)
    have hgW : activePatternGuarded P.xi P.L W (c (N+1)) P.z kind := by
      by_contra h
      exact he (Or.inr h)
    have hgT := guarded_mono_upper P.xi_lt_one hT.2 (c (N+1)) P.z kind hgW
    have hclose (k : Fin 4) :
        |(fullCategoryCount activeFocalPrefix kind k:ℝ)-(N+1:ℕ)*P.categories.mass k|<
          (N+1:ℕ)*δ := by
      have hh := lt_of_not_ge (fun h => hcount ⟨k,h⟩)
      simpa only [fullCategoryCount,Nat.cast_add] using hh
    have hA : |(Fintype.card (ActivePatternIndex kind):ℝ)-(N+1:ℕ)*P.a|≤
        (N+1:ℕ)*δ := by
      simpa [Finish01.Primitives.categories,LowBody.categoryLaw_mass,
        activePattern_count_active] using (hclose 1).le
    have hH0 : |(activePatternUpper kind 0:ℝ)-(N+1:ℕ)*(P.h/2)|≤
        (N+1:ℕ)*δ := by
      have hh := (hclose 2).le
      rw [show fullCategoryCount activeFocalPrefix kind 2=activePatternUpper kind 0 from
        activePattern_count_upper kind 0] at hh
      simpa [Finish01.Primitives.categories,LowBody.categoryLaw_mass] using hh
    have hH1 : |(activePatternUpper kind 1:ℝ)-(N+1:ℕ)*(P.h/2)|≤
        (N+1:ℕ)*δ := by
      have hh := (hclose 3).le
      rw [show fullCategoryCount activeFocalPrefix kind 3=activePatternUpper kind 1 from
        activePattern_count_upper kind 1] at hh
      simpa [Finish01.Primitives.categories,LowBody.categoryLaw_mass] using hh
    have hm := hmenu (Fintype.card (ActivePatternIndex kind))
      (activePatternUpper kind 0) (activePatternUpper kind 1) hA hH0 hH1
      hgW.2.1 (ActivePatternIndex kind) rfl (activePatternFocal kind) G hGW b hbW v hv
    rw [patternInterim_guarded_eq P.xi_pos P.xi_lt_one P.L_pos
      P.z (c (N+1)) kind F G hgT v b]
    apply le_of_lt
    simpa only [R,Finish01.Primitives.reference,Finish01.Primitives.h0,
        Finish01.Primitives.qbar,Finish01.Primitives.eta,
        activePatternResidual,activePatternSmall,activePatternQuota,activePatternGap,
        activePatternCapacity,activeResidual] using hm.1
  have hcountBound := forced_fractional_count_exception_le P.categories
    activeFocalPrefix N hδ.le (by simpa only [Nat.cast_one] using hpre)
  have hguardBound := (hguard (Measure.dirac (0:ℝ)) inferInstance).2
  have hE : (CommonList.iid P.categories N).prob E≤
      8*Real.exp (-(N:ℝ)*δ^2/2)+activeGuardExceptionError P.h δg δeq N := by
    have hu := (CommonList.iid P.categories N).prob_union_le
      (activePatternCountException P.categories δ)
      (fun kind => ¬activePatternGuarded P.xi P.L W (c (N+1)) P.z kind)
    exact hu.trans (add_le_add hcountBound hguardBound)
  have he := finite_expect_error_le (CommonList.iid P.categories N) E
    (fun kind => patternInterim P.xi P.z P.L T (c (N+1)) kind F G v b)
    R (ε/2) C (half_pos hε).le hgood hbad
  apply he.trans_lt
  have hprob := hE.trans_lt hsmall
  have hmul := mul_lt_mul_of_pos_left hprob hC
  have hdiv : C*(ε/(2*C))=ε/2 := by field_simp
  rw [hdiv] at hmul
  linarith

end FCAppendix.Affine.Hybrid.Finishing01Menus
