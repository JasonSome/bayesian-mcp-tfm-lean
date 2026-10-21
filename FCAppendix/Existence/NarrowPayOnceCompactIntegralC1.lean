import FCAppendix.Existence.NarrowPayOnceLocalOptimal

noncomputable section
namespace FCAppendix.Existence.NarrowPayOnce
open Set Filter Topology MeasureTheory Metric

theorem contDiffAt_integral_of_compact_rows {Omega : Type*}
    [TopologicalSpace Omega] [MeasurableSpace Omega] [BorelSpace Omega]
    [TopologicalSpace.MetrizableSpace Omega] [CompactSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (f : (ℝ×ℝ)→Omega→ℝ) (g : (ℝ×ℝ)→Omega→((ℝ×ℝ)→L[ℝ] ℝ))
    (s : Set (ℝ×ℝ)) (hs : IsOpen s)
    (hf : ∀t∈s,Continuous (f t))
    (hg : ContinuousOn (fun t : (ℝ×ℝ)×Omega=>g t.1 t.2) (s×ˢuniv))
    (hd : ∀t∈s,∀omega,HasFDerivAt (fun x=>f x omega) (g t omega) t)
    (t0 : ℝ×ℝ) (ht0 : t0∈s) :
    ContDiffAt ℝ 1 (fun t=>∫omega,f t omega ∂mu) t0 := by
  obtain ⟨r,hr,hrsub⟩ := Metric.mem_nhds_iff.mp (hs.mem_nhds ht0)
  let u := ball t0 (r/2)
  let v := closedBall t0 (r/2)
  have hu : u∈𝓝 t0 := ball_mem_nhds _ (half_pos hr)
  have huv : u⊆v := ball_subset_closedBall
  have hvs : v⊆s := by
    intro t ht
    apply hrsub
    change dist t t0≤r/2 at ht
    change dist t t0<r
    linarith
  have hgs := hg.mono (Set.prod_mono hvs (Subset.refl _))
  obtain ⟨B,hB⟩ := ((isCompact_closedBall t0 (r/2)).prod
    (isCompact_univ : IsCompact (univ : Set Omega))).bddAbove_image hgs.norm
  have gcont (t : ℝ×ℝ) (ht : t∈s) : Continuous (g t) := by
    apply ContinuousOn.comp_continuous hg (continuous_const.prodMk continuous_id)
    intro omega
    exact ⟨ht,mem_univ _⟩
  have gbound (t : ℝ×ℝ) (ht : t∈v) (omega : Omega) : ‖g t omega‖≤B :=
    hB ⟨(t,omega),⟨ht,mem_univ _⟩,rfl⟩
  have hcont : ContinuousOn (fun t=>∫omega,g t omega ∂mu) u := by
    apply continuousOn_of_dominated
      (bound:=fun _ : Omega=>B)
      (fun t ht=>(gcont t (hvs (huv ht))).aestronglyMeasurable)
      (fun t ht=>ae_of_all _ (gbound t (huv ht))) (integrable_const B)
    apply ae_of_all
    intro omega
    apply hg.comp (continuous_id.prodMk continuous_const).continuousOn
    intro t ht
    exact ⟨hvs (huv ht),mem_univ _⟩
  apply contDiffAt_one_iff.mpr
  refine ⟨fun t=>∫omega,g t omega ∂mu,u,hu,hcont,?_⟩
  intro t ht
  have hut : u∈𝓝 t := isOpen_ball.mem_nhds ht
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le (s:=u)
    (bound:=fun _ : Omega=>B) hut
  · filter_upwards [hut] with x hx
    exact (hf x (hvs (huv hx))).aestronglyMeasurable
  · exact (ContinuousMap.equivBoundedOfCompact _ _ ⟨_,hf t (hvs (huv ht))⟩).integrable mu
  · exact (gcont t (hvs (huv ht))).aestronglyMeasurable
  · exact ae_of_all _ (fun omega x hx=>gbound x (huv hx) omega)
  · exact integrable_const B
  · exact ae_of_all _ (fun omega x hx=>hd x (hvs (huv hx)) omega)

end FCAppendix.Existence.NarrowPayOnce
