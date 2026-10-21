import FCAppendix.Affine.Hybrid.NativeAllocationCounts

noncomputable section
namespace FCAppendix.Affine.Hybrid.NativeContinuation
open MeasureTheory ProbabilityTheory Game Set Classical Bayes LowBody
variable {m : ℕ}

theorem private_pair_expected_payoff (ξ w : ℝ) (b : Fin m → ℝ) (i : Fin m)
    (f g : unitInterval → Finset (Fin m)) (hf:Measurable f) (hg:Measurable g) :
    (∫s : Fin 2 → unitInterval,purePayoff (1-ξ) w b (f (s 0),g (s 1)) i
      ∂Measure.pi (fun _ : Fin 2=>(volume : Measure unitInterval)))=
      let p:=∫s : unitInterval,(if i∈f s then (1:ℝ) else 0) ∂volume
      let q:=∫s : unitInterval,(if i∈g s then (1:ℝ) else 0) ∂volume
      w*(p+q-p*q)-b i*(p+q-2*ξ*p*q):=by
  let u : unitInterval → ℝ:=fun s=>if i∈f s then 1 else 0
  let v : unitInterval → ℝ:=fun s=>if i∈g s then 1 else 0
  have hu:Measurable u:=Measurable.ite
    (hf (MeasurableSet.of_discrete : MeasurableSet {S : Finset (Fin m)|i∈S})) measurable_const measurable_const
  have hv:Measurable v:=Measurable.ite
    (hg (MeasurableSet.of_discrete : MeasurableSet {S : Finset (Fin m)|i∈S})) measurable_const measurable_const
  have hiu:Integrable u (volume : Measure unitInterval):=by
    apply Integrable.of_bound hu.aestronglyMeasurable 1
    exact ae_of_all _ (fun s=>by dsimp only [u];split <;> norm_num)
  have hiv:Integrable v (volume : Measure unitInterval):=by
    apply Integrable.of_bound hv.aestronglyMeasurable 1
    exact ae_of_all _ (fun s=>by dsimp only [v];split <;> norm_num)
  let P:=(volume : Measure unitInterval).prod (volume : Measure unitInterval)
  have hiuP:Integrable (fun s : unitInterval×unitInterval=>u s.1) P:=by
    simpa only [mul_one] using hiu.mul_prod (integrable_const (1:ℝ) : Integrable (fun _ : unitInterval=>(1:ℝ)) volume)
  have hivP:Integrable (fun s : unitInterval×unitInterval=>v s.2) P:=by
    simpa only [one_mul] using (integrable_const (1:ℝ) : Integrable (fun _ : unitInterval=>(1:ℝ)) volume).mul_prod hiv
  have hiuv:Integrable (fun s : unitInterval×unitInterval=>u s.1*v s.2) P:=hiu.mul_prod hiv
  have huInt:(∫s : unitInterval×unitInterval,u s.1 ∂P)=∫s,u s ∂(volume : Measure unitInterval):=by
    have hh:=integral_prod_mul (μ:=(volume : Measure unitInterval)) (ν:=(volume : Measure unitInterval)) u (fun _=>(1:ℝ))
    simpa only [mul_one,integral_const,probReal_univ,smul_eq_mul] using hh
  have hvInt:(∫s : unitInterval×unitInterval,v s.2 ∂P)=∫s,v s ∂(volume : Measure unitInterval):=by
    have hh:=integral_prod_mul (μ:=(volume : Measure unitInterval)) (ν:=(volume : Measure unitInterval)) (fun _=>(1:ℝ)) v
    simpa only [one_mul,integral_const,probReal_univ,smul_eq_mul] using hh
  have huvInt:(∫s : unitInterval×unitInterval,u s.1*v s.2 ∂P)=
      (∫s,u s ∂(volume : Measure unitInterval))*(∫s,v s ∂(volume : Measure unitInterval)):=integral_prod_mul u v
  let H : unitInterval×unitInterval → ℝ:=fun s=>purePayoff (1-ξ) w b (f s.1,g s.2) i
  have hH:Measurable H:=(measurable_of_countable (fun Q : Finset (Fin m)×Finset (Fin m)=>
      purePayoff (1-ξ) w b Q i)).comp ((hf.comp measurable_fst).prodMk (hg.comp measurable_snd))
  have he (s : unitInterval×unitInterval) : H s=
      w*(u s.1+v s.2-u s.1*v s.2)-b i*(u s.1+v s.2-2*ξ*(u s.1*v s.2)):=by
    by_cases h0:i∈f s.1
    · by_cases h1:i∈g s.2
      · simp [H,purePayoff,focalCopy,u,v,h0,h1]
        ring
      · simp [H,purePayoff,focalCopy,u,v,h0,h1]
    · by_cases h1:i∈g s.2
      · simp [H,purePayoff,focalCopy,u,v,h0,h1]
      · simp [H,purePayoff,focalCopy,u,v,h0,h1]
  have hprod:(∫s,H s ∂P)=
      w*((∫s,u s ∂(volume : Measure unitInterval))+(∫s,v s ∂(volume : Measure unitInterval))-
        (∫s,u s ∂(volume : Measure unitInterval))*(∫s,v s ∂(volume : Measure unitInterval)))-
      b i*((∫s,u s ∂(volume : Measure unitInterval))+(∫s,v s ∂(volume : Measure unitInterval))-
        2*ξ*((∫s,u s ∂(volume : Measure unitInterval))*(∫s,v s ∂(volume : Measure unitInterval)))):=by
    simp_rw [he]
    have hsub:=integral_sub (((hiuP.add hivP).sub hiuv).const_mul w)
      (((hiuP.add hivP).sub (hiuv.const_mul (2*ξ))).const_mul (b i))
    have hs0:=integral_sub (hiuP.add hivP) hiuv
    have hs1:=integral_sub (hiuP.add hivP) (hiuv.const_mul (2*ξ))
    have hadd:=integral_add hiuP hivP
    simp only [Pi.sub_apply,Pi.add_apply] at hsub hs0 hs1 hadd
    rw [hsub,integral_const_mul,integral_const_mul,hs0,hs1,hadd,integral_const_mul,huInt,hvInt,huvInt]
  have hp:=measurePreserving_piFinTwo (fun _ : Fin 2=>(volume : Measure unitInterval))
  have hmap:=integral_map (μ:=Measure.pi (fun _ : Fin 2=>(volume : Measure unitInterval))) hp.measurable.aemeasurable hH.aestronglyMeasurable
  rw [hp.map_eq] at hmap
  change (∫s,H (MeasurableEquiv.piFinTwo (fun _ : Fin 2=>unitInterval) s)
    ∂Measure.pi (fun _ : Fin 2=>(volume : Measure unitInterval)))=_
  rw [←hmap,hprod]
  dsimp only [u,v]
  ring

end FCAppendix.Affine.Hybrid.NativeContinuation
