import FCAppendix.Affine.Tail04.EqualSortedReceiptLaw
import FCAppendix.Affine.Tail04.FixedAmbientNoise
import FCAppendix.Affine.Tail04.ClosedNullExpectations
import FCAppendix.Affine.Tail04.FiniteTailNoisyGame

noncomputable section
namespace FCAppendix.Affine.Tail04.EqualZeroNoisePrivate
open MeasureTheory ProbabilityTheory Set Filter Topology Classical
open Existence.Distributional EqualPrivateSignal PrivatePayoffContinuity
open CompactSourceBidLaws FixedAmbientNoise

variable (D : FiniteTailNoisyGame.Data) (N H : ℕ) (vL vU : ℝ)

abbrev Own := Icc vL vU×Icc D.R D.Up
abbrev Prior := WeakProbability.Law (Signal H D.R D.V)
abbrev Parameters := Noise D.eps×Prior D H
abbrev Sample := Own D vL vU×((Fin N→ Icc (1:ℝ) D.B)×(Signal H D.R D.V×unitInterval))

local instance rivalBorel : BorelSpace
    ((Fin N → Icc (1:ℝ) D.B) × (Signal H D.R D.V × unitInterval)) := by
  haveI : BorelSpace (Signal H D.R D.V × unitInterval) := inferInstance
  exact Prod.borelSpace

local instance rivalOpens : OpensMeasurableSpace
    ((Fin N → Icc (1:ℝ) D.B) × (Signal H D.R D.V × unitInterval)) :=
  Prod.opensMeasurableSpace

local instance priorSingleton : MeasurableSingletonClass (Prior D H) := by
  haveI : T2Space (Prior D H) :=
    (WeakProbability.homeomorph (X:=Signal H D.R D.V)).symm.t2Space
  exact ⟨fun x => isClosed_singleton.measurableSet⟩

local instance sampleBorel : BorelSpace (Sample D N H vL vU) := by
  haveI : BorelSpace ((Fin N → Icc (1:ℝ) D.B) × (Signal H D.R D.V × unitInterval)) :=
    inferInstance
  exact Prod.borelSpace

def input (j : Fin H) (action : C(Own D vL vU,Icc D.R D.Up))
    (z : Parameters D H×Sample D N H vL vU) : Input N H D.R D.V :=
  (fun i=>(SortedAllNoise.sortedBox z.2.2.1 i:ℝ),
    policyMean N H D.c D.R D.V D.ξ 1 D.B (SortedAllNoise.sortedBox z.2.2.1,z.1.2),
    Function.update z.2.2.2.1 j (Sum.inr
      (physical D.hR D.hRUp (z.1.1,action z.2.1,z.2.2.2.2))))

lemma continuous_input (j : Fin H) (action : C(Own D vL vU,Icc D.R D.Up)) :
    Continuous (input D N H vL vU j action) := by
  have hb : Continuous (fun z : Parameters D H×Sample D N H vL vU=> SortedAllNoise.sortedBox z.2.2.1) :=
    SortedAllNoise.continuous_sortedBox.comp (by fun_prop)
  have hm : Continuous (fun z : Parameters D H×Sample D N H vL vU=> z.1.2) := by fun_prop
  have hq := (continuous_policyMean N H D.c D.R D.V D.ξ 1 D.B D.hξ (by norm_num)).comp
    (hb.prodMk hm)
  have he : Continuous (fun z : Parameters D H×Sample D N H vL vU => z.1.1) := by fun_prop
  have ha : Continuous (fun z : Parameters D H×Sample D N H vL vU => action z.2.1) := by fun_prop
  have hu : Continuous (fun z : Parameters D H×Sample D N H vL vU => z.2.2.2.2) := by fun_prop
  have hp : Continuous (fun z : Parameters D H×Sample D N H vL vU=>
      physical D.hR D.hRUp (z.1.1,action z.2.1,z.2.2.2.2)) :=
    (continuous_physical D.hR D.hRUp).comp (he.prodMk (ha.prodMk hu))
  exact (continuous_pi (fun i=> continuous_subtype_val.comp ((continuous_apply i).comp hb))).prodMk
    (hq.prodMk ((by fun_prop : Continuous (fun z : Parameters D H×Sample D N H vL vU=>
      z.2.2.2.1)).update j (continuous_inr.comp hp)))

def payoff (j : Fin H) (action : C(Own D vL vU,Icc D.R D.Up))
    (z : Parameters D H×Sample D N H vL vU) : ℝ :=
  ((z.2.1.1:ℝ)-(physical D.hR D.hRUp (z.1.1,action z.2.1,z.2.2.2.2):ℝ))*
    privateValue (c:=D.c) D.ξ j (input D N H vL vU j action z)

lemma measurable_payoff (j : Fin H) (action : C(Own D vL vU,Icc D.R D.Up)) :
    Measurable (payoff D N H vL vU j action) := by
  apply Measurable.mul
  · unfold physical EqualPrivateAmbient.widen noisyBid Hybrid.activeNoisyRealBid
    exact (by fun_prop : Continuous (fun z : Parameters D H×Sample D N H vL vU=>
      (z.2.1.1:ℝ)-(action z.2.1:ℝ)*(1+(z.1.1:ℝ)*(z.2.2.2.2:ℝ)))).measurable
  · exact (measurable_privateValue D.ξ j).comp
      (continuous_input D N H vL vU j action).measurable

def bad (j : Fin H) (action : C(Own D vL vU,Icc D.R D.Up)) :
    Set (Parameters D H×Sample D N H vL vU) :=
  input D N H vL vU j action ⁻¹' (Regular (N:=N) (R:=D.R) (Rp:=D.V) D.ξ j)ᶜ

lemma isClosed_bad (j : Fin H) (action : C(Own D vL vU,Icc D.R D.Up)) :
    IsClosed (bad D N H vL vU j action) :=
  (isOpen_regular (N:=N) (R:=D.R) (Rp:=D.V) D.ξ j).isClosed_compl.preimage
    (continuous_input D N H vL vU j action)

lemma continuousAt_payoff (j : Fin H) (action : C(Own D vL vU,Icc D.R D.Up))
    (z : Parameters D H×Sample D N H vL vU) (hz : z∉bad D N H vL vU j action) :
    ContinuousAt (payoff D N H vL vU j action) z := by
  have hr : input D N H vL vU j action z∈Regular D.ξ j := by
    simpa only [bad,Set.mem_preimage,Set.mem_compl_iff,not_not] using hz
  apply ContinuousAt.mul
  · exact (by fun_prop : Continuous (fun z : Parameters D H×Sample D N H vL vU=>
      (z.2.1.1:ℝ)-(action z.2.1:ℝ)*(1+(z.1.1:ℝ)*(z.2.2.2.2:ℝ)))).continuousAt
  · exact (continuousAt_privateValue (c:=D.c) D.ξ j _ hr).comp
      (continuous_input D N H vL vU j action).continuousAt

lemma payoff_bound (j : Fin H) (action : C(Own D vL vU,Icc D.R D.Up))
    (z : Parameters D H×Sample D N H vL vU) :
    |payoff D N H vL vU j action z|≤|vL|+|vU|+|D.V| := by
  have hv : |(z.2.1.1:ℝ)|≤|vL|+|vU| := by
    apply abs_le.mpr
    have hvl:=z.2.1.1.2.1
    have hvu:=z.2.1.1.2.2
    constructor <;> nlinarith [le_abs_self vL,neg_le_abs vL,le_abs_self vU,abs_nonneg vL,abs_nonneg vU]
  have hp : |(physical D.hR D.hRUp (z.1.1,action z.2.1,z.2.2.2.2):ℝ)|≤|D.V| := by
    rw [abs_of_nonneg (D.hR.le.trans (physical D.hR D.hRUp _).2.1)]
    exact (physical D.hR D.hRUp _).2.2.trans (le_abs_self _)
  have hq:=privateValue_bounds (c:=D.c) D.ξ j (input D N H vL vU j action z)
  unfold payoff
  rw [abs_mul,abs_of_nonneg hq.1]
  exact (mul_le_of_le_one_right (abs_nonneg _) hq.2).trans
    ((abs_sub _ _).trans (by linarith))

def sampleLaw (π : ProbabilityMeasure (Own D vL vU))
    (ν : ProbabilityMeasure (Icc (1:ℝ) D.B)) (θ : ProbabilityMeasure (Signal H D.R D.V)) :
    ProbabilityMeasure (Sample D N H vL vU) :=
  productLaw π (productLaw (rowLaw N ν) (productLaw θ uniformLaw))

lemma continuous_sampleLaw : Continuous
    (fun z : ProbabilityMeasure (Own D vL vU)×ProbabilityMeasure (Icc (1:ℝ) D.B)×
        ProbabilityMeasure (Signal H D.R D.V)=> sampleLaw D N H vL vU z.1 z.2.1 z.2.2) := by
  let T := ProbabilityMeasure (Own D vL vU) × ProbabilityMeasure (Icc (1:ℝ) D.B) ×
    ProbabilityMeasure (Signal H D.R D.V)
  have hc : Continuous (fun z : T => productLaw z.2.2 uniformLaw) :=
    (continuous_productLaw (X:=Signal H D.R D.V) (Y:=unitInterval)).comp
      ((continuous_snd.comp continuous_snd).prodMk continuous_const)
  have hr : Continuous (fun z : T =>
      productLaw (rowLaw N z.2.1) (productLaw z.2.2 uniformLaw)) :=
    (continuous_productLaw (X:=Fin N → Icc (1:ℝ) D.B)
      (Y:=Signal H D.R D.V × unitInterval)).comp
        (((continuous_rowLaw N).comp (continuous_fst.comp continuous_snd)).prodMk hc)
  exact (continuous_productLaw (X:=Own D vL vU)
    (Y:=(Fin N → Icc (1:ℝ) D.B) × (Signal H D.R D.V × unitInterval))).comp
      (continuous_fst.prodMk hr)

theorem ae_zero_regular (j : Fin H) (action : C(Own D vL vU,Icc D.R D.Up))
    (μ : Prior D H)
    (hμ : ∀ a : ℝ,0< a→∀ᵐ s ∂WeakProbability.toMeasure μ,∀ k,partialBid (s k)≠a)
    (ν : ProbabilityMeasure (Icc (1:ℝ) D.B)) [NullSingletonClass (ν : Measure (Icc (1:ℝ) D.B))]
    (θ : ProbabilityMeasure (Signal H D.R D.V))
    (hθ : ∀ a : ℝ,0< a→∀ᵐ s ∂(θ : Measure (Signal H D.R D.V)),∀ k,partialBid (s k)≠a)
    (π : ProbabilityMeasure (Own D vL vU)) :
    ∀ᵐ x ∂(sampleLaw D N H vL vU π ν θ : Measure (Sample D N H vL vU)),
      input D N H vL vU j action ((zero D.eps D.heps.le,μ),x)∈Regular D.ξ j := by
  change ∀ᵐ x ∂(π : Measure (Own D vL vU)).prod
    ((rowLaw N ν : Measure (Fin N → Icc (1:ℝ) D.B)).prod ((θ : Measure (Signal H D.R D.V)).prod (volume : Measure unitInterval))),_
  apply (Measure.ae_prod_iff_ae_ae (by
    exact (isOpen_regular (N:=N) (R:=D.R) (Rp:=D.V) D.ξ j).measurableSet.preimage
      ((continuous_input D N H vL vU j action).comp (by fun_prop)).measurable)).mpr
  apply ae_of_all
  intro own
  have ha : 0<(action own:ℝ) := D.hR.trans_le (action own).2.1
  have hr := EqualSortedReceiptLaw.ae_sorted_receipts_ne (N:=N) (c:=D.c) D.hξ D.hξ1 μ hμ ν (action own:ℝ)
  rw [←rowLaw_eq_pi] at hr
  apply (Measure.ae_prod_iff_ae_ae (by
    exact (isOpen_regular (N:=N) (R:=D.R) (Rp:=D.V) D.ξ j).measurableSet.preimage
      ((continuous_input D N H vL vU j action).comp (by fun_prop)).measurable)).mpr
  filter_upwards [hr] with common hcommon
  apply (Measure.ae_prod_iff_ae_ae (by
    exact (isOpen_regular (N:=N) (R:=D.R) (Rp:=D.V) D.ξ j).measurableSet.preimage
      ((continuous_input D N H vL vU j action).comp (by fun_prop)).measurable)).mpr
  filter_upwards [hθ (action own) ha] with privateRowValue hprivate
  apply ae_of_all
  intro u
  refine ⟨?_,?_⟩
  · simpa only [input,Function.update_self,partialBid,physical_zero,EqualPrivateAmbient.widen] using ha
  · intro k hk
    cases k with
    | inl i =>
      simpa only [input,itemReceipt,Function.update_self,partialBid,physical_zero,
        EqualPrivateAmbient.widen,EqualReceiptLaw.receipt] using hcommon i
    | inr l =>
      have hlj : l≠j := fun he=> hk (congrArg Sum.inr he)
      simpa only [input,itemReceipt,Function.update_self,Function.update_of_ne hlj,partialBid,
        physical_zero,EqualPrivateAmbient.widen] using hprivate l

theorem bad_zero_null (j : Fin H) (action : C(Own D vL vU,Icc D.R D.Up))
    (μ : Prior D H)
    (hμ : ∀ a : ℝ,0< a→∀ᵐ s ∂WeakProbability.toMeasure μ,∀ k,partialBid (s k)≠a)
    (ν : ProbabilityMeasure (Icc (1:ℝ) D.B)) [NullSingletonClass (ν : Measure (Icc (1:ℝ) D.B))]
    (θ : ProbabilityMeasure (Signal H D.R D.V))
    (hθ : ∀ a : ℝ,0< a→∀ᵐ s ∂(θ : Measure (Signal H D.R D.V)),∀ k,partialBid (s k)≠a)
    (π : ProbabilityMeasure (Own D vL vU)) :
    (ClosedNullExpectations.experiment (zero D.eps D.heps.le,μ)
      (sampleLaw D N H vL vU π ν θ) : Measure _)
        (bad D N H vL vU j action)=0 := by
  apply measure_eq_zero_iff_ae_notMem.mpr
  change ∀ᵐ z ∂(Measure.dirac (zero D.eps D.heps.le,μ)).prod
    (sampleLaw D N H vL vU π ν θ : Measure (Sample D N H vL vU)),z∉bad D N H vL vU j action
  apply (Measure.ae_prod_iff_ae_ae (isClosed_bad D N H vL vU j action).measurableSet.compl).mpr
  rw [MeasureTheory.ae_dirac_eq]
  change ∀ᵐ x ∂(sampleLaw D N H vL vU π ν θ : Measure (Sample D N H vL vU)),
    ((zero D.eps D.heps.le,μ),x) ∉ bad D N H vL vU j action
  filter_upwards [ae_zero_regular D N H vL vU j action μ hμ ν θ hθ π] with x hx
  simpa only [bad,Set.mem_preimage,Set.mem_compl_iff,not_not] using hx

theorem tendsto_payoff_test (j : Fin H)
    (action : C(Own D vL vU,Icc D.R D.Up)) (a : C(Own D vL vU,ℝ))
    (eps : ℕ→ Noise D.eps) (heps : Tendsto eps atTop (𝓝 (zero D.eps D.heps.le)))
    (μn : ℕ→ Prior D H) (μ : Prior D H) (hμn : Tendsto μn atTop (𝓝 μ))
    (hμ : ∀ x : ℝ,0< x→∀ᵐ s ∂WeakProbability.toMeasure μ,∀ k,partialBid (s k)≠x)
    (νn : ℕ→ ProbabilityMeasure (Icc (1:ℝ) D.B))
    (ν : ProbabilityMeasure (Icc (1:ℝ) D.B)) [NullSingletonClass (ν : Measure (Icc (1:ℝ) D.B))]
    (hν : Tendsto νn atTop (𝓝 ν))
    (θn : ℕ→ ProbabilityMeasure (Signal H D.R D.V))
    (θ : ProbabilityMeasure (Signal H D.R D.V)) (hθn : Tendsto θn atTop (𝓝 θ))
    (hθ : ∀ x : ℝ,0< x→∀ᵐ s ∂(θ : Measure (Signal H D.R D.V)),∀ k,partialBid (s k)≠x)
    (πn : ℕ→ ProbabilityMeasure (Own D vL vU)) (π : ProbabilityMeasure (Own D vL vU))
    (hπ : Tendsto πn atTop (𝓝 π)) :
    Tendsto (fun n=>∫ x,a x.1*payoff D N H vL vU j action ((eps n,μn n),x)
      ∂(sampleLaw D N H vL vU (πn n) (νn n) (θn n) : Measure _)) atTop
      (𝓝 (∫ x,a x.1*payoff D N H vL vU j action ((zero D.eps D.heps.le,μ),x)
        ∂(sampleLaw D N H vL vU π ν θ : Measure (Sample D N H vL vU)))) := by
  let aa : C(Parameters D H×Sample D N H vL vU,ℝ) :=
    ⟨fun z=> a z.2.1,a.continuous.comp (continuous_fst.comp continuous_snd)⟩
  have hs : Tendsto (fun n=> sampleLaw D N H vL vU (πn n) (νn n) (θn n)) atTop
      (𝓝 (sampleLaw D N H vL vU π ν θ)) :=
    (continuous_sampleLaw D N H vL vU).continuousAt.tendsto.comp
      (hπ.prodMk_nhds (hν.prodMk_nhds hθn))
  exact ClosedNullExpectations.tendsto_localized
    (payoff D N H vL vU j action) (measurable_payoff D N H vL vU j action)
    (bad D N H vL vU j action) (isClosed_bad D N H vL vU j action)
    (continuousAt_payoff D N H vL vU j action) (by positivity)
    (payoff_bound D N H vL vU j action) (fun n=>(eps n,μn n))
    (zero D.eps D.heps.le,μ) (heps.prodMk_nhds hμn)
    (fun n=> sampleLaw D N H vL vU (πn n) (νn n) (θn n))
    (sampleLaw D N H vL vU π ν θ) hs
    (bad_zero_null D N H vL vU j action μ hμ ν θ hθ π) aa

end FCAppendix.Affine.Tail04.EqualZeroNoisePrivate
