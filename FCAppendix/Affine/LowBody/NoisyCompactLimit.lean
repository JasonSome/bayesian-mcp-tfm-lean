import FCAppendix.Affine.LowBody.NoisyRow
import Mathlib.MeasureTheory.Measure.Portmanteau

noncomputable section
namespace FCAppendix.Affine.LowBody
open MeasureTheory ProbabilityTheory Set Filter Topology
open Existence.Distributional

theorem lowNoisyLaw_bid_le_value (d ε : ℝ) (hε : 0<ε) (hsmall : ε≤1/2)
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu]
    (pi : Law (A:=unitInterval) mu) :
    ∀ᵐz ∂((lowNoisyLaw d ε hε hsmall mu pi).1 : Measure (LowValue d×LowValue d)),z.2.1≤z.1.1 := by
  let psi : (LowValue d×unitInterval)×unitInterval→LowValue d×LowValue d :=
    fun x=>(x.1.1,noisyBid d ε hε hsmall x)
  have hm : Measurable psi := (measurable_fst.comp measurable_fst).prodMk
    (continuous_noisyBid d ε hε hsmall).measurable
  have hS : MeasurableSet {z : LowValue d×LowValue d | z.2.1≤z.1.1} :=
    measurableSet_le (measurable_snd.subtype_val) (measurable_fst.subtype_val)
  change ∀ᵐz ∂(((pi.1 : Measure (LowValue d×unitInterval)).prod
    (volume : Measure unitInterval)).map psi),z.2.1≤z.1.1
  apply (ae_map_iff hm.aemeasurable hS).mpr
  exact ae_of_all _ (fun x=>(noisyBid_bounds hε hsmall x.1.1 x.1.2 x.2).2)

theorem limit_bid_le_value {d : ℝ}
    (pi : ℕ→ProbabilityMeasure (LowValue d×LowValue d))
    (pi₀ : ProbabilityMeasure (LowValue d×LowValue d))
    (ht : Tendsto pi atTop (𝓝 pi₀))
    (hs : ∀j,∀ᵐz ∂(pi j : Measure (LowValue d×LowValue d)),z.2.1≤z.1.1) :
    ∀ᵐz ∂(pi₀ : Measure (LowValue d×LowValue d)),z.2.1≤z.1.1 := by
  let O : Set (LowValue d×LowValue d):={z | z.1.1<z.2.1}
  have ho : IsOpen O := isOpen_lt (continuous_fst.subtype_val) (continuous_snd.subtype_val)
  have hz (j : ℕ) : (pi j : Measure (LowValue d×LowValue d)) O=0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    exact (hs j).mono (fun _ hh hn=>not_lt_of_ge hh hn)
  have hp:=ProbabilityMeasure.le_liminf_measure_open_of_tendsto ht ho
  simp_rw [hz] at hp
  rw [liminf_const] at hp
  have hzero : (pi₀ : Measure (LowValue d×LowValue d)) O=0 := le_antisymm hp bot_le
  exact (measure_eq_zero_iff_ae_notMem.mp hzero).mono (fun _ hh=>le_of_not_gt hh)

theorem exists_actual_noisy_low_limit {N : ℕ} (d : ℝ)
    {ξ : ℝ} (hξ : 0<ξ) (hξ1 : ξ<1) (c : ℕ) (categories : FiniteLaw (Fin 4))
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu] :
    ∃(eps : ℕ→ℝ)(heps : ∀j,0<eps j)(hsmall : ∀j,eps j≤1/2)
      (pi : ℕ→Law (A:=unitInterval) mu)(pi₀ : Law (A:=LowValue d) mu),
      (∀j,eps j≤1/4) ∧ Tendsto eps atTop (𝓝 0) ∧
      (∀j,∃sigma : Kernel (LowValue d) unitInterval,
        IsMarkovKernel sigma ∧ mu⊗ₘsigma=((pi j).1 : Measure (LowValue d×unitInterval)) ∧
        (∀ᵐw ∂mu,∀ᵐq ∂sigma w,∀q' : unitInterval,
          noisyExpectedUtility (N:=N) d ξ (eps j) (heps j) (hsmall j) c categories mu (pi j,(w,q'))≤
            noisyExpectedUtility (N:=N) d ξ (eps j) (heps j) (hsmall j) c categories mu (pi j,(w,q)))) ∧
      Tendsto (fun j=>(lowNoisyLaw d (eps j) (heps j) (hsmall j) mu (pi j)).1)
        atTop (𝓝 pi₀.1) ∧
      (∀ᵐz ∂(pi₀.1 : Measure (LowValue d×LowValue d)),z.2.1≤z.1.1) := by
  letI : Nonempty (LowValue d):=nonempty_of_isProbabilityMeasure mu
  let eps : ℕ→ℝ:=fun j=>(1/4)/(j+1)
  have heps : ∀j,0<eps j:=by intro j; dsimp [eps]; positivity
  have hquarter : ∀j,eps j≤1/4 := by
    intro j
    dsimp [eps]
    apply (div_le_iff₀ (by positivity : (0:ℝ)<j+1)).mpr
    nlinarith [show (0:ℝ)≤j from Nat.cast_nonneg j]
  have hsmall : ∀j,eps j≤1/2:=fun j=>(hquarter j).trans (by norm_num)
  have heps0 : Tendsto eps atTop (𝓝 0) := by
    have hc : Tendsto (fun _ : ℕ=>(1/4:ℝ)) atTop (𝓝 (1/4:ℝ)):=tendsto_const_nhds
    convert (hc.mul (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ))) using 1
    · funext j; dsimp [eps]; ring
    · simp
  choose pi sigma hmark hdis hopt using
    (fun j=>exists_noisy_restricted_low_law (N:=N) d hξ hξ1 (heps j) (hsmall j) c categories mu)
  let actual : ℕ→Law (A:=LowValue d) mu:=fun j=>lowNoisyLaw d (eps j) (heps j) (hsmall j) mu (pi j)
  obtain ⟨pi₀,phi,hphi,hlim⟩:=CompactSpace.tendsto_subseq actual
  have ht : Tendsto (fun j=>(actual (phi j)).1) atTop (𝓝 pi₀.1) :=
    continuous_subtype_val.continuousAt.tendsto.comp hlim
  refine ⟨eps ∘ phi,(fun j=>heps (phi j)),(fun j=>hsmall (phi j)),pi ∘ phi,pi₀,
    (fun j=>hquarter (phi j)),heps0.comp hphi.tendsto_atTop,?_,ht,?_⟩
  · intro j
    exact ⟨sigma (phi j),hmark (phi j),hdis (phi j),hopt (phi j)⟩
  · exact limit_bid_le_value (fun j=>(actual (phi j)).1) pi₀.1 ht
      (fun j=>lowNoisyLaw_bid_le_value d (eps (phi j)) (heps (phi j)) (hsmall (phi j)) mu (pi (phi j)))

end FCAppendix.Affine.LowBody
