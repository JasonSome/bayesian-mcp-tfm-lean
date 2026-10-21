import FCAppendix.Affine.LowBody.CarrierRowTransport
import FCAppendix.Affine.LowBody.ExpectedClusterLoss

noncomputable section
namespace FCAppendix.Affine.LowBody
open MeasureTheory Set
variable {A : Type*} [MeasurableSpace A] {N : ℕ}

theorem carrier_intervalLoss_expectation (c : ℕ) {κ U : ℝ} (hκ : 1/2 ≤ κ) (hU : 0 ≤ U)
    (s a h : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ a) (hh : 0 ≤ h) (hsum : s+a+h=1)
    (G : Measure ℝ) [IsProbabilityMeasure G]
    (Gamma : Measure A) [IsFiniteMeasure Gamma] (x z : A→ℝ)
    (hx : Measurable x) (hz : Measurable z) (B C : Set ℝ)
    (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hbox : ∀ᵐt ∂Gamma,0 ≤ x t ∧ x t ≤ U ∧ Icc (x t) (z t)⊆B ∧ Icc (κ*x t) (κ*z t)⊆C) :
    (∫q : (Fin N→RowRival)×(A×RowRival),
      rowIntervalLoss c κ (x q.2.1) (z q.2.1) (Fin.cons q.2.2 q.1)
      ∂(Measure.pi (fun _ : Fin N=>rivalLaw s a h G)).prod (Gamma.prod (rivalLaw s a h G))) ≤
      Gamma.real univ*((2*κ-1)*U*(N+1:ℕ)*s*(G.real B+G.real C)*
        (CommonList.iid (categoryLaw s a h hs ha hh hsum G) N).prob (BothUnderflow c)) := by
  classical
  let rho:=rivalLaw s a h G
  let nu:=Measure.pi (fun _ : Fin N=>rho)
  let P:=nu.prod (Gamma.prod rho)
  let E:=harmfulCluster (N:=N) c (B∪C)
  let cost:=(2*κ-1)*U
  letI : IsProbabilityMeasure rho:=rivalLaw_isProbability s a h hs ha hh hsum G
  have hc : 0 ≤ cost:=mul_nonneg (by linarith) hU
  have hE : MeasurableSet E:=measurableSet_harmfulCluster_set c (B∪C) (hB.union hC)
  have hboxabs : ∀ᵐt ∂Gamma,|x t| ≤ U:=hbox.mono (fun _ ht=>by rw [abs_of_nonneg ht.1];exact ht.2.1)
  have hiL:=integrable_literalCarrierLoss c κ nu Gamma rho x z hx hz U hU hboxabs
  have hmI : Measurable (E.indicator (fun _=>cost)):=measurable_const.indicator hE
  have hiI : Integrable (fun q : (Fin N→RowRival)×(A×RowRival)=>
      E.indicator (fun _=>cost) (Fin.cons q.2.2 q.1)) P := by
    apply Integrable.of_bound (hmI.comp measurable_cons_carrier_row).aestronglyMeasurable cost
    exact ae_of_all _ (fun q=>by
      change |E.indicator (fun _=>cost) (Fin.cons q.2.2 q.1)|≤cost
      by_cases he : (Fin.cons q.2.2 q.1 : Fin (N+1)→RowRival)∈E
      · simp only [Set.indicator_of_mem he,abs_of_nonneg hc,le_refl]
      · simp only [Set.indicator_of_notMem he,abs_zero]
        exact hc)
  have hboxP:=(measurePreserving_snd (μ:=nu) (ν:=Gamma.prod rho)).quasiMeasurePreserving.ae
    ((measurePreserving_fst (μ:=Gamma) (ν:=rho)).quasiMeasurePreserving.ae hbox)
  have hle:=integral_mono_ae hiL hiI (by
    filter_upwards [hboxP] with q hq
    exact rowIntervalLoss_le_cluster_indicator c hκ hq.1 hq.2.1 (z q.2.1) B C
      hq.2.2.1 hq.2.2.2 (Fin.cons q.2.2 q.1))
  let f : A×(Fin (N+1)→RowRival)→ℝ:=fun p=>E.indicator (fun _=>cost) p.2
  have hf : Measurable f:=hmI.comp measurable_snd
  have hiFull : Integrable f (Gamma.prod (Measure.pi (fun _ : Fin (N+1)=>rho))) := by
    apply Integrable.of_bound hf.aestronglyMeasurable cost
    exact ae_of_all _ (fun p=>by
      rw [Real.norm_eq_abs]
      by_cases he : p.2∈E
      · simp only [f,Set.indicator_of_mem he,abs_of_nonneg hc,le_refl]
      · simp only [f,Set.indicator_of_notMem he,abs_zero]
        exact hc)
  have htransport:=integral_carrierRow Gamma rho f hf hiFull
  have hnorm : (∫q : (Fin N→RowRival)×(A×RowRival),
      E.indicator (fun _=>cost) (Fin.cons q.2.2 q.1) ∂P)=
      Gamma.real univ*(∫omega,E.indicator (fun _=>cost) omega
        ∂Measure.pi (fun _ : Fin (N+1)=>rho)) := by
    rw [htransport]
    dsimp only [f]
    rw [integral_const]
    rfl
  rw [hnorm] at hle
  have hcluster:=expected_two_cluster_loss s a h hs ha hh hsum G (N:=N) c B C hB hC cost hc
  exact hle.trans (mul_le_mul_of_nonneg_left hcluster (measureReal_nonneg))

end FCAppendix.Affine.LowBody
