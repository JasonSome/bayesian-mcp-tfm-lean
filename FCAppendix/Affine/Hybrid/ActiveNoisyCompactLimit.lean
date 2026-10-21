import FCAppendix.Affine.Hybrid.ActiveNoisyRow

noncomputable section
namespace FCAppendix.Affine.Hybrid
open MeasureTheory ProbabilityTheory Set Filter Topology
open Existence.Distributional

abbrev ActiveUniversalBid (L U : ℝ) := Icc L (2*U)

def activeUniversalNoisyBid {vlo vhi L U : ℝ} (hL : 0<L) (hLU : L≤U)
    (x : unitInterval × ((ActiveValue vlo vhi × ActiveBaseBid L U) × unitInterval)) :
    ActiveUniversalBid L U := by
  have hh:=activeNoisyRealBid_mem hL x.1.property.1 x.2.1.2 x.2.2
  refine ⟨activeNoisyRealBid x.1 x.2.1.2 x.2.2,hh.1,hh.2.trans ?_⟩
  have hU : 0≤U:=hL.le.trans hLU
  nlinarith [x.1.property.2]

lemma continuous_activeUniversalNoisyBid {vlo vhi L U : ℝ} (hL : 0<L) (hLU : L≤U) :
    Continuous (activeUniversalNoisyBid (vlo:=vlo) (vhi:=vhi) hL hLU) := by
  apply Continuous.subtype_mk
  unfold activeNoisyRealBid
  fun_prop

def activeUniversalNoisyLaw {vlo vhi L U : ℝ} (hL : 0<L) (hLU : L≤U)
    (mu : Measure (ActiveValue vlo vhi)) [IsProbabilityMeasure mu]
    (p : unitInterval × Law (A:=ActiveBaseBid L U) mu) : Law (A:=ActiveUniversalBid L U) mu :=
  noisyLaw mu (⟨volume,inferInstance⟩ : ProbabilityMeasure unitInterval)
    (fun x=>activeUniversalNoisyBid hL hLU (p.1,x))
    ((continuous_activeUniversalNoisyBid hL hLU).comp (continuous_const.prodMk continuous_id)) p.2

lemma activeUniversalNoisyBid_val {vlo vhi L U : ℝ} (hL : 0<L) (hLU : L≤U)
    (eps : unitInterval) (x : (ActiveValue vlo vhi × ActiveBaseBid L U) × unitInterval) :
    (activeUniversalNoisyBid hL hLU (eps,x):ℝ)=(activeNoisyBid hL eps.property.1 x:ℝ) := rfl

def activeUniversalBaseBid {L U : ℝ} (hL : 0<L) (hLU : L≤U) (B : ActiveBaseBid L U) :
    ActiveUniversalBid L U := ⟨B,B.property.1,B.property.2.trans (by linarith)⟩

lemma continuous_activeUniversalBaseBid {L U : ℝ} (hL : 0<L) (hLU : L≤U) :
    Continuous (activeUniversalBaseBid hL hLU) := continuous_subtype_val.subtype_mk _

lemma activeUniversalNoisyBid_zero {vlo vhi L U : ℝ} (hL : 0<L) (hLU : L≤U)
    (x : (ActiveValue vlo vhi × ActiveBaseBid L U) × unitInterval) :
    activeUniversalNoisyBid hL hLU (0,x)=activeUniversalBaseBid hL hLU x.1.2 := by
  apply Subtype.ext
  change (x.1.2:ℝ)*(1+(0:ℝ)*(x.2:ℝ))=(x.1.2:ℝ)
  ring

theorem activeUniversalNoisyLaw_zero {vlo vhi L U : ℝ} (hL : 0<L) (hLU : L≤U)
    (mu : Measure (ActiveValue vlo vhi)) [IsProbabilityMeasure mu]
    (pi : Law (A:=ActiveBaseBid L U) mu) :
    activeUniversalNoisyLaw hL hLU mu (0,pi)=pushLaw mu
      (fun t=>activeUniversalBaseBid hL hLU t.2)
      ((continuous_activeUniversalBaseBid hL hLU).comp continuous_snd) pi := by
  apply Subtype.ext
  apply Subtype.ext
  change (((pi.1 : Measure (ActiveValue vlo vhi × ActiveBaseBid L U)).prod
      (volume : Measure unitInterval)).map (fun x=>(x.1.1,activeUniversalNoisyBid hL hLU (0,x))))=
    (pi.1 : Measure (ActiveValue vlo vhi × ActiveBaseBid L U)).map
      (fun t=>(t.1,activeUniversalBaseBid hL hLU t.2))
  have he : (fun x : (ActiveValue vlo vhi × ActiveBaseBid L U) × unitInterval=>
      (x.1.1,activeUniversalNoisyBid hL hLU (0,x)))=
      (fun t : ActiveValue vlo vhi × ActiveBaseBid L U=>
        (t.1,activeUniversalBaseBid hL hLU t.2))∘Prod.fst := by
    funext x
    rw [activeUniversalNoisyBid_zero]
    rfl
  have hg : Measurable (fun t : ActiveValue vlo vhi × ActiveBaseBid L U=>
      (t.1,activeUniversalBaseBid hL hLU t.2)) := measurable_fst.prodMk
        ((continuous_activeUniversalBaseBid hL hLU).comp continuous_snd).measurable
  rw [he,←Measure.map_map hg measurable_fst,Measure.map_fst_prod,measure_univ,one_smul]

theorem continuous_activeUniversalNoisyLaw {vlo vhi L U : ℝ} (hL : 0<L) (hLU : L≤U)
    (mu : Measure (ActiveValue vlo vhi)) [IsProbabilityMeasure mu] :
    Continuous (activeUniversalNoisyLaw hL hLU mu) := by
  apply Continuous.subtype_mk
  apply ProbabilityMeasure.continuous_iff_forall_continuousMap_continuous_integral.mpr
  intro f
  let inner : (unitInterval × (ActiveValue vlo vhi × ActiveBaseBid L U)) × unitInterval→ℝ:=
    fun x=>f (x.1.2.1,activeUniversalNoisyBid hL hLU (x.1.1,(x.1.2,x.2)))
  have hinner : Continuous inner := by
    apply f.continuous.comp
    apply (show Continuous (fun x : (unitInterval × (ActiveValue vlo vhi × ActiveBaseBid L U)) × unitInterval=>x.1.2.1) from by fun_prop).prodMk
    exact (continuous_activeUniversalNoisyBid hL hLU).comp
      ((show Continuous (fun x : (unitInterval × (ActiveValue vlo vhi × ActiveBaseBid L U)) × unitInterval=>x.1.1) from by fun_prop).prodMk
        ((show Continuous (fun x : (unitInterval × (ActiveValue vlo vhi × ActiveBaseBid L U)) × unitInterval=>x.1.2) from by fun_prop).prodMk continuous_snd))
  let g : unitInterval × (ActiveValue vlo vhi × ActiveBaseBid L U)→ℝ:=
    fun x=>∫z : unitInterval,inner (x,z)
  let theta : ProbabilityMeasure unitInterval:=⟨volume,inferInstance⟩
  have hp : Continuous (fun x : unitInterval × (ActiveValue vlo vhi × ActiveBaseBid L U)=>(x,theta)) :=
    continuous_id.prodMk continuous_const
  have hg : Continuous g:= (continuous_law_integral inner hinner).comp hp
  have hc : Continuous (fun p : unitInterval × Law (A:=ActiveBaseBid L U) mu=>
      ∫x,g (p.1,x) ∂(p.2.1 : Measure (ActiveValue vlo vhi × ActiveBaseBid L U))) :=
    (continuous_law_integral g hg).comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  convert hc using 1
  funext p
  exact integral_noisyLaw mu (⟨volume,inferInstance⟩ : ProbabilityMeasure unitInterval)
    (fun x=>activeUniversalNoisyBid hL hLU (p.1,x))
    ((continuous_activeUniversalNoisyBid hL hLU).comp (continuous_const.prodMk continuous_id))
    p.2 f f.continuous

theorem exists_actual_noisy_active_limit {N : ℕ} {d vlo vhi L U xi : ℝ}
    (hL : 0<L) (hLU : L≤U) (hxi : 0<xi) (hxi1 : xi<1)
    (z : ℝ) (c : ℕ) (categories : FiniteLaw (Fin 4))
    (lowLaw : ProbabilityMeasure (LowBody.LowValue d))
    (mu : Measure (ActiveValue vlo vhi)) [IsProbabilityMeasure mu] :
    ∃(eps : ℕ→unitInterval)(pi : ℕ→Law (A:=ActiveBaseBid L U) mu)
      (pi0 : Law (A:=ActiveBaseBid L U) mu),
      (∀j,0<(eps j:ℝ)) ∧ Tendsto eps atTop (𝓝 0) ∧
      (∀j,∃sigma : Kernel (ActiveValue vlo vhi) (ActiveBaseBid L U),
        IsMarkovKernel sigma ∧ mu⊗ₘsigma=((pi j).1 : Measure (ActiveValue vlo vhi × ActiveBaseBid L U)) ∧
        (∀ᵐv ∂mu,∀ᵐB ∂sigma v,∀B' : ActiveBaseBid L U,
          activeNoisyExpectedUtility (N:=N) hL (eps j).property.1 xi z c categories lowLaw mu (pi j,(v,B'))≤
            activeNoisyExpectedUtility (N:=N) hL (eps j).property.1 xi z c categories lowLaw mu (pi j,(v,B)))) ∧
      Tendsto pi atTop (𝓝 pi0) ∧
      Tendsto (fun j=>activeUniversalNoisyLaw hL hLU mu (eps j,pi j)) atTop
        (𝓝 (activeUniversalNoisyLaw hL hLU mu (0,pi0))) := by
  letI : Nonempty (ActiveBaseBid L U):=⟨⟨L,le_rfl,hLU⟩⟩
  let epsR : ℕ→ℝ:=fun j=>(1/4)/(j+1)
  have hpos : ∀j,0<epsR j:=by intro j;dsimp [epsR];positivity
  have hsmall : ∀j,epsR j≤1:=by
    intro j
    dsimp [epsR]
    apply (div_le_iff₀ (by positivity : (0:ℝ)<j+1)).mpr
    have hn : (0:ℝ)≤j:=Nat.cast_nonneg j
    linarith
  let eps : ℕ→unitInterval:=fun j=>⟨epsR j,(hpos j).le,hsmall j⟩
  have heps0 : Tendsto eps atTop (𝓝 0) := by
    apply tendsto_subtype_rng.mpr
    have hc : Tendsto (fun _ : ℕ=>(1/4:ℝ)) atTop (𝓝 (1/4:ℝ)):=tendsto_const_nhds
    convert hc.mul (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)) using 1
    · funext j;dsimp [eps,epsR];ring
    · simp
  choose pi sigma hmark hdis hopt using (fun j=>exists_noisy_active_pattern_law (N:=N)
    hL hLU (hpos j) hxi hxi1 z c categories lowLaw mu)
  obtain ⟨pi0,phi,hphi,hlim⟩:=CompactSpace.tendsto_subseq pi
  refine ⟨eps∘phi,pi∘phi,pi0,(fun j=>hpos (phi j)),heps0.comp hphi.tendsto_atTop,?_,hlim,?_⟩
  · intro j
    exact ⟨sigma (phi j),hmark (phi j),hdis (phi j),hopt (phi j)⟩
  · exact (continuous_activeUniversalNoisyLaw hL hLU mu).continuousAt.tendsto.comp
      ((heps0.comp hphi.tendsto_atTop).prodMk_nhds hlim)

end FCAppendix.Affine.Hybrid
