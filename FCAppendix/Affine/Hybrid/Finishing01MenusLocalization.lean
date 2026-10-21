import FCAppendix.Affine.Hybrid.Finishing01MenusNoisyTransport

set_option maxHeartbeats 6000000
set_option synthInstance.maxSize 1000
noncomputable section
namespace FCAppendix.Affine.Hybrid.Finishing01Menus
open MeasureTheory ProbabilityTheory Set Filter Topology Classical
open Existence.Distributional
open scoped BigOperators

variable (P : Finish01.Primitives)

theorem exists_enlarged_menu_box (r : ℝ) (hr : 0< r) :
    ∃W : ℝ, P.U< W ∧ W< P.U+r ∧ W< P.vlo ∧
      P.kappa*W< P.h0*P.L ∧ P.h0*W< P.L := by
  let top := min (P.U+r) (min P.vlo (min (P.h0*P.L/P.kappa) (P.L/P.h0)))
  have htop : P.U< top := by
    refine lt_min (by linarith) (lt_min P.value_surplus (lt_min ?_ ?_))
    · exact (lt_div_iff₀ P.kappa_pos).mpr
        (by simpa only [Finish01.Primitives.kappa,Finish01.Primitives.h0,
          Finish01.Primitives.qbar,mul_comm] using P.box_lower)
    · exact (lt_div_iff₀ P.h0_pos).mpr
        (by simpa only [Finish01.Primitives.h0,Finish01.Primitives.qbar,mul_comm]
          using P.box_upper)
  obtain ⟨W,hUW,hWt⟩ := exists_between htop
  have hWr := hWt.trans_le (min_le_left _ _)
  have hrest := hWt.trans_le (min_le_right _ _)
  have hWv := hrest.trans_le (min_le_left _ _)
  have hrest' := hrest.trans_le (min_le_right _ _)
  have hWk := (lt_div_iff₀ P.kappa_pos).mp (hrest'.trans_le (min_le_left _ _))
  have hWh := (lt_div_iff₀ P.h0_pos).mp (hrest'.trans_le (min_le_right _ _))
  exact ⟨W,hUW,hWr,hWv,by nlinarith,by nlinarith⟩

theorem harmonic_price_bounds (G : Measure ℝ) [IsProbabilityMeasure G]
    {T : ℝ} (hLT : P.L≤ T) (hG : ∀ᵐb∂G,b∈ Icc P.L T) :
    P.h0/reciprocalMean G∈ Icc (P.h0*P.L) (P.h0*T) := by
  have hT : 0< T := P.L_pos.trans_le hLT
  have hH := reciprocalMean_bounds G P.L_pos hG
  have hHp : 0< reciprocalMean G := (one_div_pos.mpr hT).trans_le hH.1
  constructor
  · apply (le_div_iff₀ hHp).mpr
    have hh := mul_le_mul_of_nonneg_left hH.2 (mul_pos P.h0_pos P.L_pos).le
    have he : P.h0*P.L*(1/P.L)=P.h0 := by field_simp [P.L_pos.ne']
    nlinarith only [hh,he]
  · apply (div_le_iff₀ hHp).mpr
    have hh := mul_le_mul_of_nonneg_left hH.1 (mul_pos P.h0_pos hT).le
    have he : P.h0*T*(1/T)=P.h0 := by field_simp [hT.ne']
    nlinarith only [hh,he]

theorem reference_uniform_modulus (e : ℝ) (he : 0< e) :
    ∃δ>0,∀ v∈ Icc P.vlo P.vhi,
      ∀ lam∈ Icc (P.h0*P.L) (P.h0*(P.U+1)),
      ∀ lam'∈ Icc (P.h0*P.L) (P.h0*(P.U+1)),
      ∀ b∈ Icc P.L (P.U+1),∀ b'∈ Icc P.L (P.U+1),
      |lam-lam'|<δ → |b-b'|<δ →
        |P.reference v lam b-P.reference v lam' b'|< e := by
  let S : Set ((ℝ×ℝ)×ℝ) :=
    (Icc P.vlo P.vhi ×ˢ Icc (P.h0*P.L) (P.h0*(P.U+1))) ×ˢ Icc P.L (P.U+1)
  have hS : IsCompact S := (isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc
  have hcont : ContinuousOn
      (fun p : (ℝ×ℝ)×ℝ => P.reference p.1.1 p.1.2 p.2) S := by
    intro p hp
    have hb : p.2≠0 := (P.L_pos.trans_le hp.2.1).ne'
    have hξ : P.xi≠0 := P.xi_pos.ne'
    unfold Finish01.Primitives.reference independentTwo exposure
    fun_prop
  obtain ⟨δ,hδ,hm⟩ := Metric.uniformContinuousOn_iff.mp
    (hS.uniformContinuousOn_of_continuous hcont) e he
  refine ⟨δ,hδ,?_⟩
  intro v hv lam hlam lam' hlam' b hb b' hb' hl hd
  have hh := hm ((v,lam),b) ⟨⟨hv,hlam⟩,hb⟩
    ((v,lam'),b') ⟨⟨hv,hlam'⟩,hb'⟩
  apply (show |P.reference v lam b-P.reference v lam' b'|< e from ?_)
  simpa only [Real.dist_eq] using hh (by
    simp only [Prod.dist_eq,Real.dist_eq,sub_self,abs_zero,
      max_eq_right (abs_nonneg (lam-lam'))]
    exact max_lt hl hd)

theorem exists_prelimit_uniform_reference (c : ℕ→ℕ)
    (hc : Tendsto (fun M => (c M:ℝ)/(M:ℝ)) atTop (𝓝 P.rho))
    (e : ℝ) (he : 0< e) :
    ∃ε₀>0,∀ᶠN in atTop,∀(ε : ℝ) (hε : ε∈ Icc (0:ℝ) ε₀),
      ∀(low : ProbabilityMeasure P.Low)
        (mu : Measure P.Value) [IsProbabilityMeasure mu]
        (pi : Law (A:=P.Bid) mu),
      ∃lam∈ Icc (P.h0*P.L) (P.h0*P.U),∀ v : P.Value,∀ b : P.Bid,
        |activeNoisyExpectedUtility (N:=N) P.L_pos hε.1
            P.xi P.z (c (N+1)) P.categories low mu (pi,(v,b))-
          P.reference v lam b|≤ e := by
  have h0pos : 0< P.h0 := P.h0_pos
  have hUpos : 0< P.U := P.U_pos
  have hLpos : 0< P.L := P.L_pos
  obtain ⟨δ,hδ,hmod⟩ := reference_uniform_modulus P (e/2) (half_pos he)
  let r := min 1 (δ/(2*(P.h0+1)))
  have hr : 0< r := lt_min zero_lt_one (by positivity)
  obtain ⟨W,hUW,hWr,_hWv,hboxlo,hboxhi⟩ := exists_enlarged_menu_box P r hr
  have hLW : P.L≤ W := P.L_lt_U.le.trans hUW.le
  have hW1 : W< P.U+1 := by
    have hh := min_le_left (1:ℝ) (δ/(2*(P.h0+1)))
    dsimp only [r] at hWr
    linarith
  have hgapδ : (W-P.U)*(2*(P.h0+1))<δ := by
    have hh : W-P.U<δ/(2*(P.h0+1)) := by
      have hm := min_le_right (1:ℝ) (δ/(2*(P.h0+1)))
      dsimp only [r] at hWr
      linarith
    exact (lt_div_iff₀ (by positivity)).mp hh
  have hgap : 0< W-P.U := sub_pos.mpr hUW
  have hWδ : W-P.U<δ := by nlinarith [P.h0_pos]
  have hhδ : P.h0*(W-P.U)<δ := by nlinarith [P.h0_pos]
  let ε₀ := (W-P.U)/(2*P.U)
  have hε₀ : 0<ε₀ := div_pos hgap (by positivity)
  have hεeq : ε₀*P.U=(W-P.U)/2 := by dsimp [ε₀]; field_simp
  let V := |P.vlo|+|P.vhi|
  have hV : 0≤ V := by dsimp [V]; positivity
  have hfinite := full_row_reference_limit P W hLW hboxlo hboxhi c hc V hV (e/2) (half_pos he)
  refine ⟨ε₀,hε₀,?_⟩
  filter_upwards [hfinite] with N hN
  intro ε hε low mu _ pi
  let G := implementedReal P hε.1 mu pi
  let T := P.U*(1+ε)
  have hTG : ∀ᵐb∂G,b∈ Icc P.L T := implementedReal_box P hε.1 mu pi
  have hT : T∈ Icc P.L W := by
    have hh := mul_le_mul_of_nonneg_right hε.2 P.U_pos.le
    rw [hεeq] at hh
    constructor
    · dsimp [T]
      nlinarith [P.L_lt_U,P.U_pos,hε.1]
    · dsimp [T]
      nlinarith
  let lp := P.h0/reciprocalMean G
  let lam := min lp (P.h0*P.U)
  have hlp := harmonic_price_bounds P G hT.1 hTG
  have hlam : lam∈ Icc (P.h0*P.L) (P.h0*P.U) := by
    refine ⟨le_min hlp.1 (mul_le_mul_of_nonneg_left P.L_lt_U.le P.h0_pos.le),min_le_right _ _⟩
  have hlpd : |lp-lam|<δ := by
    have hlo : 0≤ lp-lam := sub_nonneg.mpr (min_le_left _ _)
    rw [abs_of_nonneg hlo]
    by_cases hh : lp≤ P.h0*P.U
    · simp only [lam,min_eq_left hh,sub_self]
      exact hδ
    · have ht := mul_le_mul_of_nonneg_left hT.2 P.h0_pos.le
      have hl := hlp.2.trans ht
      simp only [lam,min_eq_right (le_of_not_ge hh)]
      linarith
  have hlpbig : lp∈ Icc (P.h0*P.L) (P.h0*(P.U+1)) :=
    ⟨hlp.1,hlp.2.trans (mul_le_mul_of_nonneg_left (hT.2.trans hW1.le) P.h0_pos.le)⟩
  have hlambig : lam∈ Icc (P.h0*P.L) (P.h0*(P.U+1)) :=
    ⟨hlam.1,hlam.2.trans (mul_le_mul_of_nonneg_left (by linarith) P.h0_pos.le)⟩
  refine ⟨lam,hlam,?_⟩
  intro v b
  have hv : |(v:ℝ)|≤ V := by
    rw [abs_of_pos (P.value_pos v)]
    have hh := v.property.2.trans (le_abs_self P.vhi)
    dsimp [V]
    linarith [abs_nonneg P.vlo]
  have hpoint (z : unitInterval) :
      |actualRowInterim (N:=N) P.xi P.z P.L T (c (N+1)) P.categories
        (lowReal P low) G v (activeNoisyRealBid ε b z)-P.reference v lam b|≤ e := by
    have hbp := activeNoisyRealBid_mem P.L_pos hε.1 b z
    have hfirst := hN T hT (lowReal P low) G hTG v hv
      (activeNoisyRealBid ε b z) hbp
    have hd : |activeNoisyRealBid ε b z-(b:ℝ)|<δ := by
      have hb0 := P.bid_pos b
      have hze := mul_nonneg hε.1 z.property.1
      have hz1 := mul_le_mul_of_nonneg_left z.property.2 hε.1
      have hbb := mul_le_mul_of_nonneg_left hz1 hb0.le
      have hbu := mul_le_mul_of_nonneg_right b.property.2 hε.1
      have hsmall := mul_le_mul_of_nonneg_right hε.2 P.U_pos.le
      rw [hεeq] at hsmall
      unfold activeNoisyRealBid
      rw [abs_of_nonneg (by nlinarith)]
      nlinarith
    have hsecond := hmod v v.property lp hlpbig lam hlambig
      (activeNoisyRealBid ε b z) ⟨hbp.1,hbp.2.trans (hT.2.trans hW1.le)⟩
      b ⟨b.property.1,b.property.2.trans (by linarith)⟩ hlpd hd
    exact ((abs_sub_le _ (P.reference v lp (activeNoisyRealBid ε b z)) _).trans
      (add_le_add hfirst.le hsecond.le)).trans (by linarith)
  rw [noisyExpectedUtility_eq_actualRow_noise (N:=N) P hε.1 (c (N+1)) low mu pi v b]
  have hm : Measurable (fun z : unitInterval =>
      actualRowInterim (N:=N) P.xi P.z P.L T (c (N+1)) P.categories
        (lowReal P low) G v (activeNoisyRealBid ε b z)) := by
    simpa only [Function.comp_def] using
      (measurable_actualRowInterim (N:=N) P.xi_pos P.xi_lt_one P.z P.L T
      (c (N+1)) P.categories (lowReal P low) G).comp
      (show Measurable (fun z : unitInterval => ((v : ℝ), activeNoisyRealBid ε b z)) from
        measurable_const.prodMk (by unfold activeNoisyRealBid; fun_prop))
  have hi : Integrable (fun z : unitInterval =>
      actualRowInterim (N:=N) P.xi P.z P.L T (c (N+1)) P.categories
        (lowReal P low) G v (activeNoisyRealBid ε b z)) volume := by
    apply Integrable.of_bound hm.aestronglyMeasurable (|P.reference v lam b| + e)
    filter_upwards [] with z
    rw [Real.norm_eq_abs]
    have hh := abs_add_le (actualRowInterim (N:=N) P.xi P.z P.L T (c (N+1)) P.categories
      (lowReal P low) G v (activeNoisyRealBid ε b z) - P.reference v lam b) (P.reference v lam b)
    simpa only [sub_add_cancel] using hh.trans (by have h := add_le_add (hpoint z) (le_refl |P.reference v lam b|); simpa only [add_comm] using h)
  have hh := norm_integral_le_of_norm_le_const (μ := (volume : Measure unitInterval))
    (C := e) (f := fun z : unitInterval =>
      actualRowInterim (N:=N) P.xi P.z P.L T (c (N+1)) P.categories
        (lowReal P low) G v (activeNoisyRealBid ε b z) - P.reference v lam b)
    (ae_of_all _ (fun z => by simpa only [Real.norm_eq_abs] using hpoint z))
  rw [integral_sub hi (integrable_const _), integral_const, probReal_univ, one_smul, mul_one] at hh
  simpa only [Real.norm_eq_abs] using hh

theorem ae_closed_of_tendsto {X : Type*} [MeasurableSpace X]
    [MetricSpace X] [BorelSpace X]
    (μ : ℕ→ ProbabilityMeasure X) (μ₀ : ProbabilityMeasure X)
    (ht : Tendsto μ atTop (𝓝 μ₀)) (S : Set X) (hS : IsClosed S)
    (hμ : ∀ᶠj in atTop,∀ᵐx∂(μ j:Measure X),x∈ S) :
    ∀ᵐx∂(μ₀:Measure X),x∈ S := by
  have hz : ∀ᶠj in atTop,(μ j:Measure X) Sᶜ=0 := by
    filter_upwards [hμ] with j hj
    exact measure_eq_zero_iff_ae_notMem.mpr (hj.mono (fun _ hx => not_not.mpr hx))
  have hp := ProbabilityMeasure.le_liminf_measure_open_of_tendsto ht hS.isOpen_compl
  have he : liminf (fun j => (μ j:Measure X) Sᶜ) atTop=0 := by
    rw [Filter.liminf_congr hz,liminf_const]
  rw [he] at hp
  have hzero : (μ₀:Measure X) Sᶜ=0 := le_antisymm hp bot_le
  exact (measure_eq_zero_iff_ae_notMem.mp hzero).mono (fun _ hx => not_not.mp hx)

theorem uniform_full_row_menu_and_strip (c : ℕ→ℕ)
    (hc : Tendsto (fun M => (c M:ℝ)/(M:ℝ)) atTop (𝓝 P.rho)) :
    ∃τ>0,∀ᶠM in atTop,
      ∀(low : ProbabilityMeasure P.Low)
        (mu : Measure P.Value) [IsProbabilityMeasure mu]
        (W : P.NoisyWitness M (c M) low mu),
      (∀ᶠj in atTop,∀ᵐt∂((W.noisy j).1:Measure (P.Value×P.Bid)),
        (t.2:ℝ)∈ Icc (P.L+τ) (P.U-τ)) ∧
      (∀ᵐt∂(W.joint.1:Measure (P.Value×P.Bid)),
        (t.2:ℝ)∈ Icc (P.L+τ) (P.U-τ)) := by
  obtain ⟨τ,g,hτ,_hwidth,hg,hb0,hb1,hgap⟩ := exists_uniform_endpoint_strips
    P.xi_pos P.xi_lt_one P.z_nonneg P.z_lt_one P.qbar_mem P.L_pos
    P.value_order P.value_surplus P.inward_lower P.inward_upper
  obtain ⟨ε₀,hε₀,happrox⟩ := exists_prelimit_uniform_reference P c hc (g/4) (by positivity)
  have hshift : Tendsto (fun M : ℕ => M-1) atTop atTop := by
    apply tendsto_atTop.2
    intro k
    filter_upwards [eventually_ge_atTop (k+1)] with M hM
    omega
  have hm := hshift.eventually happrox
  refine ⟨τ,hτ,?_⟩
  filter_upwards [hm,eventually_ge_atTop (1:ℕ)] with M hM hM1
  have hMc : (M-1)+1=M := by omega
  simp only [hMc] at hM
  intro low mu _ W
  have heps : ∀ᶠj in atTop,(W.eps j:ℝ)≤ε₀ := by
    have ht : Tendsto (fun j => (W.eps j:ℝ)) atTop (𝓝 0) :=
      continuous_subtype_val.tendsto _ |>.comp W.eps_zero
    exact (ht.eventually (gt_mem_nhds hε₀)).mono (fun _ h => h.le)
  let b0 : P.Bid := ⟨P.L+2*τ,hb0⟩
  let b1 : P.Bid := ⟨P.U-2*τ,hb1⟩
  have hsupport : ∀ᶠj in atTop,∀ᵐt∂((W.noisy j).1:Measure (P.Value×P.Bid)),
      (t.2:ℝ)∈ Icc (P.L+τ) (P.U-τ) := by
    filter_upwards [heps] with j hj
    obtain ⟨lam,hlam,href⟩ := hM (W.eps j:ℝ) ⟨(W.eps j).property.1,hj⟩ low mu (W.noisy j)
    obtain ⟨sigma,hmark,hdis,hIC⟩ := W.noisy_IC j
    letI := hmark
    let u : P.Value×P.Bid→ℝ := fun t => activeNoisyExpectedUtility
      (N:=M-1) P.L_pos (W.eps j).property.1 P.xi P.z (c M) P.categories low mu (W.noisy j,t)
    have hu : Continuous u := (continuous_activeNoisyExpectedUtility
      P.L_pos (W.eps_pos j) P.xi_pos P.xi_lt_one P.z (c M) P.categories low mu).comp
        (continuous_const.prodMk continuous_id)
    have hfixed (b' : P.Bid) : ∀ᵐt∂((W.noisy j).1:Measure (P.Value×P.Bid)),
        u (t.1,b')≤ u t := by
      rw [←hdis]
      apply Measure.ae_compProd_of_ae_ae
        (measurableSet_le (hu.measurable.comp (measurable_fst.prodMk measurable_const)) hu.measurable)
      filter_upwards [hIC] with v hv
      exact hv.mono (fun b hb => hb b')
    filter_upwards [hfixed b0,hfixed b1] with t ht0 ht1
    have hrefi := href t.1 t.2
    have hrefl := href t.1 b0
    have hrefu := href t.1 b1
    have gaps := hgap t.1 t.1.property lam hlam
    have hreference (b' : P.Bid) : bidMenu P.xi P.z t.1 lam b' = P.reference t.1 lam b' :=
      bidMenu_eq_physical (show P.eta = 1-2*P.xi from rfl) P.xi_pos.ne' (P.bid_pos b').ne'
    constructor
    · by_contra hl
      have hb : (t.2:ℝ)∈ Icc P.L (P.L+τ) := ⟨t.2.property.1,le_of_lt (lt_of_not_ge hl)⟩
      have hi := (abs_le.mp hrefi).2
      have hl := (abs_le.mp hrefl).1
      have hg0 := gaps.1 t.2 hb
      change activeNoisyExpectedUtility _ _ _ _ _ _ _ _ _ ≤ _ at ht0
      change bidMenu P.xi P.z t.1 lam t.2 + g ≤ bidMenu P.xi P.z t.1 lam b0 at hg0
      rw [hreference, hreference] at hg0
      dsimp only [u] at ht0
      linarith only [hi, hl, hg0, ht0, hg]
    · by_contra hu'
      have hb : (t.2:ℝ)∈ Icc (P.U-τ) P.U := ⟨le_of_lt (lt_of_not_ge hu'),t.2.property.2⟩
      have hi := (abs_le.mp hrefi).2
      have hu0 := (abs_le.mp hrefu).1
      have hg1 := gaps.2 t.2 hb
      change activeNoisyExpectedUtility _ _ _ _ _ _ _ _ _ ≤ _ at ht1
      change bidMenu P.xi P.z t.1 lam t.2 + g ≤ bidMenu P.xi P.z t.1 lam b1 at hg1
      rw [hreference, hreference] at hg1
      dsimp only [u] at ht1
      linarith only [hi, hu0, hg1, ht1, hg]
  refine ⟨hsupport,?_⟩
  have ht : Tendsto (fun j => (W.noisy j).1) atTop (𝓝 W.joint.1) :=
    continuous_subtype_val.tendsto _ |>.comp W.joint_tendsto
  exact ae_closed_of_tendsto _ _ ht
    {t : P.Value×P.Bid | (t.2:ℝ)∈ Icc (P.L+τ) (P.U-τ)}
    (isClosed_Icc.preimage (continuous_snd.subtype_val)) hsupport

theorem eventual_strip_threshold (c : ℕ→ℕ)
    (hc : Tendsto (fun M => (c M:ℝ)/(M:ℝ)) atTop (𝓝 P.rho)) :
    ∀ᶠM in atTop,∀(low : ProbabilityMeasure P.Low)
      (mu : Measure P.Value) [IsProbabilityMeasure mu]
      (W : P.NoisyWitness M (c M) low mu),
      ∃τ>0,∀ᵐt∂(W.joint.1:Measure (P.Value×P.Bid)),
        (t.2:ℝ)∈ Icc (P.L+τ) (P.U-τ) := by
  obtain ⟨τ,hτ,hall⟩ := uniform_full_row_menu_and_strip P c hc
  filter_upwards [hall] with M hM
  intro low mu _ W
  exact ⟨τ,hτ,(hM low mu W).2⟩

end FCAppendix.Affine.Hybrid.Finishing01Menus
