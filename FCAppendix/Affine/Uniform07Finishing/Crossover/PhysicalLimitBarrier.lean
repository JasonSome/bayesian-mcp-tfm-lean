import FCAppendix.Affine.Uniform07Finishing.Crossover.PhysicalOptimizer

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing.Crossover
open MeasureTheory ProbabilityTheory Bayes Game Set Filter Topology

namespace Physical

theorem U19Error_tendsto_along_market
    {market : ℕ→ℕ} {e19 : ℕ→ℝ}
    (hmarket : Tendsto market atTop atTop) (he19 : Tendsto e19 atTop (𝓝 0))
    (eta xi Amin Rmax Dmax : ℝ) :
    Tendsto (fun k => U19Error eta xi Amin Rmax Dmax (e19 k) (market k)) atTop (𝓝 0) := by
  have hcast : Tendsto (fun k => (market k:ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hmarket
  have hdiv : Tendsto (fun k => (Rmax+((1+eta/xi)/Amin)*Dmax)/(market k:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hcast
  simpa only [U19Error,mul_zero,add_zero,zero_div] using
    (hdiv.add (he19.const_mul (eta+2*((1+eta/xi)/Amin)))).div_const Amin

theorem GapLeadError_tendsto_along_market
    {market : ℕ → ℕ} {e19 e : ℕ → ℝ}
    (hmarket : Tendsto market atTop atTop)
    (he19 : Tendsto e19 atTop (𝓝 0)) (he : Tendsto e atTop (𝓝 0))
    (eta xi Amin Rmax : ℝ) :
    Tendsto (fun k => GapLeadError eta xi Amin Rmax (e19 k) (e k) (market k))
      atTop (𝓝 0) := by
  have hcast : Tendsto (fun k => (market k:ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hmarket
  have hR : Tendsto (fun k => Rmax/(market k:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hcast
  simpa only [GapLeadError,mul_zero,zero_div,add_zero] using
    ((he19.const_mul (1+eta/xi)).div_const (Amin^2)).add
      (((hR.add he19).add (he.const_mul 4)).div_const (2*Amin))

theorem eventually_literal_used_support_barrier
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
    ∀ eps>0, ∀ L'>L, ∀ᶠ k in atTop,
      ∀ b∈Icc L' R, b∈(lowerBidMeasure (Γ k) (Uniform07.cutoff row)).support →
        leadingBarrier row (Γ k) (i k) (B k) A b-
          eps/(market k:ℝ)< rank (Γ k) (Uniform07.cutoff row) b-b := by
  intro eps heps L' hLL'
  obtain ⟨k₀,hk₀⟩ := hdata.exists
  obtain ⟨E₀⟩ := hk₀.1
  have hL : 0< L := E₀.bid0
  have hcast : Tendsto (fun k => (market k:ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hmarket
  let kappa : ℝ := Uniform07.eta row/Uniform07.xi row
  let K : ℝ := (1+kappa)/Amin+1
  let omega : ℝ := eps/(8*(1+kappa))
  have hk : 0≤ kappa := div_nonneg (source_eta_mem row).1 (source_xi_pos row).le
  have hK : 0< K := by dsimp [K]; positivity
  have homega : 0< omega := by dsimp [omega]; positivity
  have hH : UniformContinuousOn (fun b => 1/A b) (Icc L R) :=
    isCompact_Icc.uniformContinuousOn_of_continuous
      (continuousOn_const.div E₀.rateContinuous (fun b hb => (hAmin.trans_le (E₀.rateBounds b hb).1).ne'))
  have hmod := hmarket.eventually (eventually_shrinking_interval_modulus hH hK.le
    (by norm_num : (0:ℝ)<1/4) omega homega)
  have hwidth : Tendsto (fun k => K/((1/4:ℝ)*(market k:ℝ))) atTop (𝓝 0) := by
    have h := (tendsto_const_nhds.div_atTop hcast :
      Tendsto (fun k => (4*K)/(market k:ℝ)) atTop (𝓝 0))
    convert h using 1
    ext k
    ring
  have hsizeLimit : Tendsto (fun k => Dmax/(market k:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hcast
  have hU19 := U19Error_tendsto_along_market hmarket he19 (Uniform07.eta row)
    (Uniform07.xi row) Amin Rmax Dmax
  have hGap := GapLeadError_tendsto_along_market hmarket he19 he
    (Uniform07.eta row) (Uniform07.xi row) Amin Rmax
  have hsGap := hGap.eventually (Iio_mem_nhds (half_pos heps))
  have hsplit : Tendsto (fun k => eS k+2*eD k/((market k:ℝ)*L*ell k/2)) atTop (𝓝 0) := by
    convert heS.add (hduplicateRent.const_mul 2) using 1 <;> try ring
    ext k
    ring
  have hres := split_absorbed_error_tendsto_zero (Nmax := 2+Dmax) heS heD hduplicateRent
  have hres' : Tendsto (fun k => eS k+3*eD k+
      (eS k+2*eD k/((market k:ℝ)*L*ell k/2))*(6+Dmax)) atTop (𝓝 0) := by
    simpa only [show (2+Dmax)+4=6+Dmax by ring] using hres
  have hs19 : ∀ᶠ k in atTop, e19 k< min (Amin/4) (1/10000) :=
    he19.eventually (Iio_mem_nhds (by positivity : (0:ℝ)< min (Amin/4) (1/10000)))
  have hse : ∀ᶠ k in atTop, e k< min (1/4) (eps*(Amin/2)/8) :=
    he.eventually (Iio_mem_nhds (by positivity : (0:ℝ)< min (1/4) (eps*(Amin/2)/8)))
  have hsS : ∀ᶠ k in atTop, eS k<1 := heS.eventually (Iio_mem_nhds (by norm_num : (0:ℝ)<1))
  have hsD : ∀ᶠ k in atTop, eD k<1 := heD.eventually (Iio_mem_nhds (by norm_num : (0:ℝ)<1))
  have hsSplit := hsplit.eventually (Iio_mem_nhds (by norm_num : (0:ℝ)<1))
  have hsRes := hres'.eventually (Iio_mem_nhds (by positivity : (0:ℝ)< eps*(Amin/2)/8))
  have hsU19 := hU19.eventually (Iio_mem_nhds (by positivity : (0:ℝ)< min 1 (eps/16)))
  have hsSize := hsizeLimit.eventually (Iio_mem_nhds (by positivity : (0:ℝ)< Amin/2))
  have hsWidth := hwidth.eventually (Iio_mem_nhds (sub_pos.mpr hLL'))
  filter_upwards [hdata,hpositive,hs19,hse,hsS,hsD,hsSplit,hsRes,hsU19,hsSize,hsWidth,hmod,
    hsGap,hmarket.eventually (eventually_ge_atTop 1)]
    with k hdk hpk h19k hek hSk hDk hsplitk hresk hUk hsizek hwidthk hmodk hGapk hmk
  obtain ⟨E⟩ := hdk.1
  obtain ⟨X⟩ := hdk.2
  rcases hpk with ⟨he19k,hek0,hellk,hSk0,hDk0⟩
  have hm : 1≤(market k:ℝ) := by exact_mod_cast hmk
  have h19small := (lt_min_iff.mp h19k).1.le
  have h19rate := (lt_min_iff.mp h19k).2.le
  have heSmall : 4*e k≤ 1 := by linarith [(lt_min_iff.mp hek).1]
  have hgapSmall : 8*e k< eps*(Amin/2) := by linarith [(lt_min_iff.mp hek).2]
  have hsmall : (1+kappa)*omega+
      2*U19Error (Uniform07.eta row) (Uniform07.xi row) Amin Rmax Dmax (e19 k) (market k)< eps/2 := by
    have hcalc : (1+kappa)*omega=eps/8 := by
      dsimp [omega]
      field_simp [show 1+kappa≠0 by positivity]
    linarith [(lt_min_iff.mp hUk).2]
  have hfinite := literal_finite_used_support_barrier E X hm hAmin he19k h19small h19rate
    hRmax hDmax hsizek.le hek0 heSmall hellk ⟨hSk0,hSk.le⟩ ⟨hDk0,hDk.le⟩
    (hSchedule k) (hFee k) heps homega.le hsplitk.le hresk.le hGapk
    (by linarith [(lt_min_iff.mp hUk).2])
    (fun a ha b hb hab hdist => (hmodk a ha b hb hab hdist).le)
    (by
      have hcalc : (1+kappa)*omega=eps/8 := by
        dsimp [omega]
        field_simp [show 1+kappa≠0 by positivity]
      linarith)
  intro b hb hbS
  apply hfinite b ⟨hLL'.le.trans hb.1,hb.2⟩ hbS
  exact hwidthk.trans_le (by linarith [hb.1])

end Physical
end FCAppendix.Affine.Uniform07Finishing.Crossover
