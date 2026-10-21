import FCAppendix.Affine.Uniform06.RankRent
import FCAppendix.PayOnce.SupportedFOC

noncomputable section

namespace FCAppendix.Affine.Uniform06.Rank

open MeasureTheory Set Filter Topology

theorem hasDerivAt_payoff
    {η v b S' D' : ℝ} {S D : ℝ → ℝ}
    (hS : HasDerivAt S S' b) (hD : HasDerivAt D D' b) :
    HasDerivAt (fun x => payoff η v x (S x) (D x))
      ((v-b)*S'-S b-η*D b-η*b*D') b := by
  have hfirst := ((hasDerivAt_id b).const_sub v).mul hS
  have hsecond := ((hasDerivAt_id b).const_mul η).mul hD
  have h := hfirst.sub hsecond
  apply h.congr_deriv
  dsimp only [id_eq]
  ring

theorem density_IC_at_supported_bid
    {η v b S' D' : ℝ} {S D : ℝ → ℝ} {Used : Set ℝ}
    (hS : HasDerivAt S S' b) (hD : HasDerivAt D D' b)
    (hl : (𝓝[Used ∩ Iio b] b).NeBot)
    (hr : (𝓝[Used ∩ Ioi b] b).NeBot)
    (hIC : ∀ x ∈ Used,
      payoff η v x (S x) (D x) ≤ payoff η v b (S b) (D b)) :
    (v-b)*S' = S b+η*D b+η*b*D' := by
  have hz := PayOnce.SupportedFOC.derivative_zero_on_two_sided_set
    (hasDerivAt_payoff hS hD) hl hr hIC
  linarith

theorem density_IC_ae_on_used_support
    {η : ℝ} {M S D S' D' : ℝ → ℝ} {Used : Set ℝ}
    (hUsed : MeasurableSet Used)
    (hS : ∀ᵐ b ∂volume, HasDerivAt S (S' b) b)
    (hD : ∀ᵐ b ∂volume, HasDerivAt D (D' b) b)
    (hIC : ∀ b ∈ Used, ∀ x ∈ Used,
      payoff η (M b) x (S x) (D x) ≤ payoff η (M b) b (S b) (D b)) :
    ∀ᵐ b ∂volume.restrict Used,
      (M b-b)*S' b = S b+η*D b+η*b*D' b := by
  have hu : ∀ᵐ b ∂volume.restrict Used, b ∈ Used := ae_restrict_mem hUsed
  have htwo := PayOnce.SupportedFOC.ae_two_sided_accumulation
    (volume.restrict Used) hu
  have hS' : ∀ᵐ b ∂volume.restrict Used, HasDerivAt S (S' b) b :=
    ae_restrict_of_ae hS
  have hD' : ∀ᵐ b ∂volume.restrict Used, HasDerivAt D (D' b) b :=
    ae_restrict_of_ae hD
  filter_upwards [hu,htwo,hS',hD'] with b hb htwo hSb hDb
  exact density_IC_at_supported_bid hSb hDb htwo.1 htwo.2 (hIC b hb)

theorem derivative_zero_ae_on_zero_set
    {F F' : ℝ → ℝ} {S : Set ℝ} (hS : MeasurableSet S)
    (hder : ∀ᵐ b ∂volume, HasDerivAt F (F' b) b)
    (hzero : ∀ b ∈ S, F b = 0) :
    ∀ᵐ b ∂volume.restrict S, F' b = 0 := by
  have hu : ∀ᵐ b ∂volume.restrict S, b ∈ S := ae_restrict_mem hS
  have htwo := PayOnce.SupportedFOC.ae_two_sided_accumulation
    (volume.restrict S) hu
  have hd : ∀ᵐ b ∂volume.restrict S, HasDerivAt F (F' b) b :=
    ae_restrict_of_ae hder
  filter_upwards [hu,htwo,hd] with b hb ht hdb
  apply PayOnce.SupportedFOC.derivative_zero_on_two_sided_set hdb ht.1 ht.2
  intro x hx
  simp only [hzero x hx,hzero b hb,le_refl]

end FCAppendix.Affine.Uniform06.Rank
