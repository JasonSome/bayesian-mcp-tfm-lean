import FCAppendix.Affine.Uniform07Finishing.Crossover.PhysicalLimitBarrier

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing.Crossover
open MeasureTheory ProbabilityTheory Bayes Game Set Filter Topology
namespace Physical

theorem eventually_actual_crossover_canonical_log_slope
    {row : Uniform07.Row} {market : ℕ→ℕ} {Seed : ℕ→ Type*}
    [∀ k, MeasurableSpace (Seed k)]
    (Γ : ∀ k, FiniteGame (market k) 2 (Uniform07.capacity (market k)) (Seed k))
    (i : ∀ k, Fin (market k)) (B : ∀ k, CanonicalEvent (Γ k))
    {L R U Amin Amax Rmax Dmax : ℝ} {A : ℝ→ℝ}
    (P : ∀ k, BroadcastLaw05 (Γ k) (Uniform07.cutoff row) U)
    {e19 e ell eS eD : ℕ→ℝ}
    (hmarket : Tendsto market atTop atTop)
    (hAmin : 0< Amin) (hRmax : 0≤ Rmax) (hDmax : 0≤ Dmax)
    (hSchedule : ∀ k, (Γ k).A=Schedule.affine 2 (Uniform07.eta row)
      (source_eta_mem row).1 (source_eta_mem row).2)
    (hFee : ∀ k, (Γ k).g=0)
    (hdata : ∀ᶠ k in atTop,
      Nonempty (RemoteKernels06 row (Γ k) (i k) (B k) L R U (P k) A
        Amin Amax Rmax Dmax (e19 k) (e k) (ell k)) ∧
      Nonempty (PureDerivativeBounds06 (Γ k) (i k) (B k) (Uniform07.cutoff row) L R (eS k) (eD k)))
    (hpositive : ∀ᶠ k in atTop, 0≤ e19 k ∧ 0≤ e k ∧ 0< ell k ∧ 0≤ eS k ∧ 0≤ eD k)
    (he19 : Tendsto e19 atTop (𝓝 0)) (he : Tendsto e atTop (𝓝 0))
    (heS : Tendsto eS atTop (𝓝 0)) (heD : Tendsto eD atTop (𝓝 0))
    (hduplicateRent : Tendsto (fun k => eD k/((market k:ℝ)*L*ell k/2)) atTop (𝓝 0)) :
    ∀ tolerance∈Ioo (0:ℝ) 1, ∀ L'>L, L'≤ R → ∀ᶠ k in atTop,
      ∀ᵐ b ∂(volume : Measure ℝ), b∈Icc L' R →
        deriv (q (Γ k) (i k)) b≤(1+tolerance)*canonicalSlope (Γ k) (i k) (B k) b*q (Γ k) (i k) b := by
  intro tolerance htolerance L' hLL' hL'R
  obtain ⟨k₀,hk₀⟩ := hdata.exists
  obtain ⟨E₀⟩ := hk₀.1
  have hAmax : 0< Amax := hAmin.trans_le ((E₀.rateBounds L ⟨le_rfl,E₀.interval⟩).1.trans
    (E₀.rateBounds L ⟨le_rfl,E₀.interval⟩).2)
  let rent0 : ℝ := 1/(4*Amax)
  let tau : ℝ := tolerance/4
  let nu : ℝ := tolerance/16
  let beta : ℝ := min (rent0/4) (rent0*tau/4)
  let C : ℝ := (6+Dmax)/rent0
  have hrent0 : 0< rent0 := by dsimp [rent0]; positivity
  have htau : 0< tau := div_pos htolerance.1 (by norm_num)
  have hnu : 0< nu := div_pos htolerance.1 (by norm_num)
  have hbeta : 0< beta := by dsimp [beta]; positivity
  have hC : 0≤ C := by dsimp [C]; positivity
  have htransport : 1+tau+nu≤(1+tolerance)*(1-nu) := by
    dsimp [tau,nu]
    nlinarith [mul_nonneg htolerance.1.le (sub_nonneg.mpr htolerance.2.le)]
  have hfirst : 2*beta≤ rent0*tau := by
    have h := min_le_right (rent0/4) (rent0*tau/4)
    dsimp [beta]
    linarith
  have hbarrier := eventually_literal_used_support_barrier Γ i B P hmarket hAmin hRmax hDmax
    hSchedule hFee hdata hpositive he19 he heS heD hduplicateRent (beta/2) (half_pos hbeta) L' hLL'
  have hcast : Tendsto (fun k => (market k:ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hmarket
  have hsize : Tendsto (fun k => Dmax/(market k:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hcast
  have hU19 := U19Error_tendsto_along_market hmarket he19 (Uniform07.eta row)
    (Uniform07.xi row) Amin Rmax Dmax
  have hsecond : Tendsto (fun k => 4*(1+C)*e k) atTop (𝓝 0) := by
    simpa only [mul_zero] using he.const_mul (4*(1+C))
  have hderivative : Tendsto (fun k => e k*(1+C)) atTop (𝓝 0) := by
    simpa only [zero_mul] using he.mul_const (1+C)
  have hevent19 := he19.eventually (Iio_mem_nhds (by positivity : (0:ℝ)< Amin/4))
  have hevent := he.eventually (Iio_mem_nhds (by positivity : (0:ℝ)< min 1 (min (rent0/4) nu)))
  have heventSize := hsize.eventually (Iio_mem_nhds (by positivity : (0:ℝ)< Amin/2))
  have heventU19 := hU19.eventually (Iio_mem_nhds (lt_min hrent0 (half_pos hbeta)))
  have heventSecond := hsecond.eventually (Iio_mem_nhds (by positivity : (0:ℝ)< rent0*(Amin/2)*tau))
  have heventDerivative := hderivative.eventually (Iio_mem_nhds (by positivity : (0:ℝ)< nu*(Amin/2)))
  filter_upwards [hdata,hpositive,hbarrier,hevent19,hevent,heventSize,heventU19,
    heventSecond,heventDerivative,hmarket.eventually (eventually_ge_atTop 1)]
    with k hdk hpk hbk h19k hek hsizek hUk hsecondk hderk hmk
  obtain ⟨E⟩ := hdk.1
  have hm : 1≤(market k:ℝ) := by exact_mod_cast hmk
  have hm0 : 0<(market k:ℝ) := by linarith
  rcases hpk with ⟨h190,he0,hell,_,_⟩
  have he1 : e k≤ 1 := (lt_min_iff.mp hek).1.le
  have heRest := lt_min_iff.mp (lt_min_iff.mp hek).2
  have habsorb : 4*e k≤ rent0 := by linarith [heRest.1]
  have hvalue : e k≤ nu := heRest.2.le
  have hrentBudget : rent0+beta+
      U19Error (Uniform07.eta row) (Uniform07.xi row) Amin Rmax Dmax (e19 k) (market k)≤ 1/Amax := by
    have hbetaMax : beta≤ rent0/4 := min_le_left _ _
    have hid : 1/Amax=4*rent0 := by dsimp [rent0]; ring
    rw [hid]
    linarith [(lt_min_iff.mp hUk).1]
  have hderBudget : e k*(1+C)≤ nu*(Amin/2)*(market k:ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hm (by positivity : 0≤ nu*(Amin/2))
    linarith
  exact actual_global_log_slope_from_used_barrier E hm hAmin h190 h19k.le hRmax hDmax hsizek.le
    he0 he1 hLL'.le hL'R hbeta.le hrent0 htau.le hnu.le habsorb hrentBudget hfirst
    hsecondk.le hvalue hderBudget (add_nonneg zero_le_one htolerance.1.le) htransport
    (by
      filter_upwards [E.canonicalAE] with b hG hb hbS
      have hbI : b∈Icc L R := ⟨hLL'.le.trans hb.1,hb.2⟩
      have hu := (E.U23 hm0 hAmin h190 h19k.le hRmax hDmax hsizek.le hbI (hG hbI)).2
      rw [← RemoteKernels06.leading_scaled hm0] at hu
      have hs := hbk b hb hbS
      have hss := mul_le_mul_of_nonneg_left hs.le hm0.le
      have hcancel : (market k:ℝ)*((beta/2)/(market k:ℝ))=beta/2 := by
        field_simp [hm0.ne']
      have hcancel' : (market k:ℝ)*(beta/(market k:ℝ))=beta := by
        field_simp [hm0.ne']
      rw [mul_sub,hcancel] at hss
      apply (mul_le_mul_iff_right₀ hm0).mp
      rw [mul_sub,hcancel']
      nlinarith [(abs_le.mp hu).2,(lt_min_iff.mp hUk).2])

theorem eventually_actual_crossover_log_slope
    {row : Uniform07.Row} {market : ℕ→ℕ} {Seed : ℕ→ Type*}
    [∀ k, MeasurableSpace (Seed k)]
    (Γ : ∀ k, FiniteGame (market k) 2 (Uniform07.capacity (market k)) (Seed k))
    (i : ∀ k, Fin (market k)) (B : ∀ k, CanonicalEvent (Γ k))
    {L R U Amin Amax Rmax Dmax : ℝ} {A : ℝ→ℝ}
    (P : ∀ k, BroadcastLaw05 (Γ k) (Uniform07.cutoff row) U)
    {e19 e ell eS eD : ℕ→ℝ}
    (hmarket : Tendsto market atTop atTop)
    (hAmin : 0< Amin) (hRmax : 0≤ Rmax) (hDmax : 0≤ Dmax)
    (hSchedule : ∀ k, (Γ k).A=Schedule.affine 2 (Uniform07.eta row)
      (source_eta_mem row).1 (source_eta_mem row).2)
    (hFee : ∀ k, (Γ k).g=0)
    (hdata : ∀ᶠ k in atTop,
      Nonempty (RemoteKernels06 row (Γ k) (i k) (B k) L R U (P k) A
        Amin Amax Rmax Dmax (e19 k) (e k) (ell k)) ∧
      Nonempty (PureDerivativeBounds06 (Γ k) (i k) (B k) (Uniform07.cutoff row) L R (eS k) (eD k)))
    (hpositive : ∀ᶠ k in atTop, 0≤ e19 k ∧ 0≤ e k ∧ 0< ell k ∧ 0≤ eS k ∧ 0≤ eD k)
    (he19 : Tendsto e19 atTop (𝓝 0)) (he : Tendsto e atTop (𝓝 0))
    (heS : Tendsto eS atTop (𝓝 0)) (heD : Tendsto eD atTop (𝓝 0))
    (hduplicateRent : Tendsto (fun k => eD k/((market k:ℝ)*L*ell k/2)) atTop (𝓝 0)) :
    ∀ tolerance∈Ioo (0:ℝ) 1, ∀ L'>L, L'≤ R → ∀ᶠ k in atTop,
      ∀ᵐ b ∂(volume : Measure ℝ), b∈Icc L' R →
        deriv (q (Γ k) (i k)) b≤(1+tolerance)*referenceSlope (market k) A b*q (Γ k) (i k) b := by
  intro tolerance htolerance L' hLL' hL'R
  let tau : ℝ := tolerance/4
  have htau : tau∈Ioo (0:ℝ) 1 := by dsimp [tau]; constructor <;> linarith [htolerance.1,htolerance.2]
  have hlog := eventually_actual_crossover_canonical_log_slope Γ i B P hmarket
    hAmin hRmax hDmax hSchedule hFee hdata hpositive he19 he heS heD hduplicateRent
    tau htau L' hLL' hL'R
  have hsmall := he19.eventually (Iio_mem_nhds
    (show (0:ℝ)< tau*Amin from mul_pos htau.1 hAmin))
  filter_upwards [hlog,hdata,hsmall,hmarket.eventually (eventually_ge_atTop 1)]
    with k hlogk hdk hek hmk
  obtain ⟨E⟩ := hdk.1
  have hm0 : 0<(market k:ℝ) := by exact_mod_cast (show 0< market k from lt_of_lt_of_le Nat.zero_lt_one hmk)
  filter_upwards [hlogk,E.canonicalAE] with b hb hG hbJ
  have hbI : b∈Icc L R := ⟨hLL'.le.trans hbJ.1,hbJ.2⟩
  have href := E.reference_slope_positive hm0 hAmin hbI
  have hq0 := q_nonneg (Γ k) (i k) b
  have hsl : canonicalSlope (Γ k) (i k) (B k) b≤(1+tau)*referenceSlope (market k) A b := by
    have hh := (abs_le.mp (hG hbI).finiteSlope).2
    have hAA := (E.rateBounds b hbI).1
    have heA : e19 k≤ tau*A b := hek.le.trans (mul_le_mul_of_nonneg_left hAA htau.1.le)
    have hs : canonicalSlope (Γ k) (i k) (B k) b/(market k:ℝ)≤(1+tau)*A b := by linarith
    have hx := (div_le_iff₀ hm0).mp hs
    dsimp [referenceSlope]
    nlinarith
  have hcoef : (1+tau)*(1+tau)≤ 1+tolerance := by
    dsimp [tau]
    nlinarith [mul_nonneg htolerance.1.le (sub_nonneg.mpr htolerance.2.le)]
  have hs := mul_le_mul_of_nonneg_right hsl hq0
  have hs' := mul_le_mul_of_nonneg_left hs (add_nonneg zero_le_one htau.1.le)
  have hc := mul_le_mul_of_nonneg_right hcoef (mul_nonneg href.le hq0)
  nlinarith [hb hbJ]

end Physical
end FCAppendix.Affine.Uniform07Finishing.Crossover
