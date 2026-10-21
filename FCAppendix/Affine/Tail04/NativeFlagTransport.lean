import FCAppendix.Affine.Tail04.UnusedBidPriceTest
import FCAppendix.Affine.Tail04.ObservableRoles
import FCAppendix.Affine.Hybrid.NativeSeed
import FCAppendix.Probability.EmpiricalConcentration

noncomputable section
namespace FCAppendix.Affine.Tail04.NativeFlag
open MeasureTheory ProbabilityTheory Set Filter Game Bayes
open Hybrid
open WeightedFlagBound
open scoped BigOperators

variable {X : Type*} [MeasurableSpace X]

def deletedUsers {N : ℕ} (i : Fin (N+1))
    (x : UserProfile (N+1) 2) : Fin N → UserDraw 2 :=
  fun j => x (i.succAbove j)

theorem deletedUsers_measurePreserving {N c : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (Γ : FiniteGame (N+1) 2 c Seed) (i : Fin (N+1)) :
    MeasurePreserving (deletedUsers i) (userProfileLaw Γ)
      (Measure.pi (fun _ : Fin N => userLaw Γ)) :=
  (measurePreserving_snd (μ := userLaw Γ)
    (ν := Measure.pi (fun _ : Fin N => userLaw Γ))).comp
      (measurePreserving_piFinSuccAbove (fun _ : Fin (N+1) => userLaw Γ) i)

theorem sample_deletedUsers_measurePreserving {N c : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (Γ : FiniteGame (N+1) 2 c Seed) (i : Fin (N+1)) :
    MeasurePreserving
      (fun x : Sample (N+1) 2 Seed => deletedUsers i x.1.1)
      (sampleLaw Γ) (Measure.pi (fun _ : Fin N => userLaw Γ)) := by
  have hprofile : MeasurePreserving
      (fun x : Background (N+1) 2 Seed => x.1)
      (backgroundLaw Γ) (userProfileLaw Γ) :=
    measurePreserving_fst (μ := userProfileLaw Γ)
      (ν := Measure.pi (fun _ : Fin 2 => Γ.seedLaw))
  have hbackground := measurePreserving_fst
    (μ := backgroundLaw Γ) (ν := permLaw 2)
  exact (deletedUsers_measurePreserving Γ i).comp (hprofile.comp hbackground)

def nativeBid (x : UserDraw 2) : ℝ := x.1.2.bid

lemma measurable_nativeBid : Measurable nativeBid :=
  (measurable_bid 2).comp measurable_fst.snd

def bulkEvent (u : ℝ) : Set (UserDraw 2) := nativeBid ⁻¹' Icc 1 (1+u)

lemma measurableSet_bulkEvent (u : ℝ) : MeasurableSet (bulkEvent u) :=
  measurable_nativeBid measurableSet_Icc

theorem iid_bulk_count_lower_tail (μ : Measure X) [IsProbabilityMeasure μ]
    (E : Set X) (hE : MeasurableSet E) (N : ℕ) (hN : 0 < N)
    {rho : ℝ} (hrho : 0 < rho) (hmass : rho ≤ μ.real E) :
    (Measure.pi (fun _ : Fin N => μ)).real
      {r | (Probability.sampleCount E r : ℝ) < rho*(N:ℝ)/2} ≤
      Real.exp (-(N:ℝ)*rho^2/2) := by
  have hn : 0 ≤ (N:ℝ) := Nat.cast_nonneg N
  have hsub : {r : Fin N → X |
      (Probability.sampleCount E r : ℝ) < rho*(N:ℝ)/2} ⊆
      {r | (Probability.sampleCount E r : ℝ) ≤ (N:ℝ)*(μ.real E-rho/2)} := by
    intro r hr
    have hh := mul_le_mul_of_nonneg_left hmass hn
    change (Probability.sampleCount E r : ℝ) < rho*(N:ℝ)/2 at hr
    change (Probability.sampleCount E r : ℝ) ≤ (N:ℝ)*(μ.real E-rho/2)
    nlinarith
  have hh := (measureReal_mono hsub).trans
    (Probability.iid_indicator_lower_tail_le μ E hE N hN (show 0 ≤ rho/2 by positivity))
  convert! hh using 1
  congr 1
  ring

theorem native_bulk_count_lower_tail {N c : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (Γ : FiniteGame (N+1) 2 c Seed) (i : Fin (N+1))
    (u : ℝ) (hN : 0 < N) {rho : ℝ} (hrho : 0 < rho)
    (hmass : rho ≤ (userLaw Γ).real (bulkEvent u)) :
    (sampleLaw Γ).real {x |
      (Probability.sampleCount (bulkEvent u) (deletedUsers i x.1.1) : ℝ) <
        rho*(N:ℝ)/2} ≤ Real.exp (-(N:ℝ)*rho^2/2) := by
  have hp := sample_deletedUsers_measurePreserving Γ i
  have hbad : MeasurableSet {r : Fin N → UserDraw 2 |
      (Probability.sampleCount (bulkEvent u) r : ℝ) < rho*(N:ℝ)/2} :=
    measurableSet_lt
      ((measurable_of_countable (fun n : ℕ => (n:ℝ))).comp
        (Probability.measurable_sampleCount (bulkEvent u) (measurableSet_bulkEvent u) N))
      measurable_const
  have he := congrArg (fun ν : Measure (Fin N → UserDraw 2) => ν.real
    {r | (Probability.sampleCount (bulkEvent u) r : ℝ) < rho*(N:ℝ)/2}) hp.map_eq
  rw [measureReal_def, Measure.map_apply hp.measurable hbad] at he
  calc
    _ = (Measure.pi (fun _ : Fin N => userLaw Γ)).real
        {r | (Probability.sampleCount (bulkEvent u) r : ℝ) < rho*(N:ℝ)/2} := by
      simpa only [measureReal_def,Set.preimage,Set.mem_setOf_eq] using he
    _ ≤ _ := iid_bulk_count_lower_tail (userLaw Γ) (bulkEvent u)
      (measurableSet_bulkEvent u) N hN hrho hmass

section FiniteKernel
variable {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω]
  [MeasurableSingletonClass Ω]

omit [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
lemma measurable_finite_probability (C : X → FiniteLaw Ω)
    (hC : ∀ omega, Measurable (fun x => (C x).mass omega))
    (P : X → Ω → Prop) (hP : ∀ omega, MeasurableSet {x | P x omega}) :
    Measurable (fun x => (C x).prob (P x)) := by
  classical
  simp only [FiniteLaw.prob_eq_expect, FiniteLaw.expect]
  exact Finset.measurable_sum _ fun omega _ =>
    (hC omega).mul (Measurable.ite (hP omega) measurable_const measurable_const)

omit [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
lemma integrable_finite_probability (μ : Measure X) [IsFiniteMeasure μ]
    (C : X → FiniteLaw Ω)
    (hC : ∀ omega, Measurable (fun x => (C x).mass omega))
    (P : X → Ω → Prop) (hP : ∀ omega, MeasurableSet {x | P x omega}) :
    Integrable (fun x => (C x).prob (P x)) μ :=
  Integrable.of_mem_Icc 0 1 (measurable_finite_probability C hC P hP).aemeasurable
    (ae_of_all _ fun x => ⟨(C x).prob_nonneg _, (C x).prob_le_one _⟩)

omit [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in

theorem integral_probability_le_bad_add (μ : Measure X) [IsProbabilityMeasure μ]
    (C : X → FiniteLaw Ω)
    (hC : ∀ omega, Measurable (fun x => (C x).mass omega))
    (P : X → Ω → Prop) (hP : ∀ omega, MeasurableSet {x | P x omega})
    (bad : Set X) (hbad : MeasurableSet bad) {K : ℝ} (hK : 0 ≤ K)
    (hgood : ∀ x, x ∉ bad → (C x).prob (P x) ≤ K) :
    (∫ x, (C x).prob (P x) ∂μ) ≤ μ.real bad+K := by
  have hbound (x : X) : (C x).prob (P x) ≤
      bad.indicator (fun _ => (1:ℝ)) x+K := by
    by_cases hx : x ∈ bad
    · simpa only [Set.indicator_of_mem hx] using
        ((C x).prob_le_one (P x)).trans (by linarith : (1:ℝ) ≤ 1+K)
    · simpa only [Set.indicator_of_notMem hx, zero_add] using hgood x hx
  have hh := integral_mono (integrable_finite_probability μ C hC P hP)
    (((integrable_const (1:ℝ)).indicator hbad).add (integrable_const K)) hbound
  change (∫ x, (C x).prob (P x) ∂μ) ≤
    ∫ x, bad.indicator (fun _ => (1:ℝ)) x+K ∂μ at hh
  rw [integral_add ((integrable_const (1:ℝ)).indicator hbad) (integrable_const K)] at hh
  have hInd : (∫ x, bad.indicator (fun _ => (1:ℝ)) x ∂μ) = μ.real bad := by
    simpa only [Set.indicator,Pi.one_apply] using (integral_indicator_one (μ := μ) hbad)
  rw [hInd,integral_const] at hh
  simpa using hh

theorem sampler_probability_integral (μ : Measure X) [IsProbabilityMeasure μ]
    (C : X → FiniteLaw Ω) (f : X → unitInterval → Ω)
    (hf : Measurable (Function.uncurry f))
    (hlaw : ∀ x, volume.map (f x) = FiniteLaw.probabilityMeasure (C x))
    (P : X → Ω → Prop)
    (hP : MeasurableSet {z : X × Ω | P z.1 z.2}) :
    (μ.prod (volume : Measure unitInterval)).real
      {z | P z.1 (f z.1 z.2)} = ∫ x, (C x).prob (P x) ∂μ := by
  classical
  let event := {z : X × unitInterval | P z.1 (f z.1 z.2)}
  have hevent : MeasurableSet event := hP.preimage (measurable_fst.prodMk hf)
  let g : X × unitInterval → ℝ := event.indicator (fun _ => 1)
  have hg : Integrable g (μ.prod (volume : Measure unitInterval)) :=
    (integrable_const (1:ℝ)).indicator hevent
  calc
    _ = ∫ z, g z ∂(μ.prod (volume : Measure unitInterval)) :=
      (integral_indicator_one hevent).symm
    _ = ∫ x, ∫ u : unitInterval, g (x,u) ∂volume ∂μ := integral_prod _ hg
    _ = _ := by
      apply integral_congr_ae
      exact ae_of_all _ fun x => by
        have hfx : Measurable (f x) := hf.comp (measurable_const.prodMk measurable_id)
        have hc := FiniteLaw.ofMeasure_eq_of_map_eq_probabilityMeasure volume
          (f x) hfx (C x) (hlaw x)
        change (∫ u : unitInterval, g (x,u) ∂volume) = (C x).prob (P x)
        rw [FiniteLaw.prob_eq_expect, ← hc, FiniteLaw.expect_ofMeasure]
        rfl

end FiniteKernel

section NativeConditionalSeed
variable {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

abbrev NonlowData (k : Fin m → Fin 4) :=
  ({i : Fin m // k i ≠ 0} → UserDraw 2) × (Fin 2 → Seed)

def nonlowLaw (Γ : FiniteGame m 2 c Seed) (E : Observable.Regions)
    (k : Fin m → Fin 4) : Measure (NonlowData (Seed:=Seed) k) :=
  (Measure.pi (fun i : {i : Fin m // k i ≠ 0} =>
    cond (userLaw Γ) (E.coarseTag ⁻¹' {k i}))).prod
      (Measure.pi (fun _ : Fin 2 => Γ.seedLaw))

def nativeLowBidLaw (Γ : FiniteGame m 2 c Seed) (E : Observable.Regions) : Measure ℝ :=
  (cond (userLaw Γ) (E.coarseTag ⁻¹' {0})).map nativeBid

def seedAndNonlow (Γ : FiniteGame m 2 c Seed) (E : Observable.Regions)
    (k : Fin m → Fin 4) (n : ℕ) (e : Fin (n+1) ≃ {i : Fin m // k i=0})
    (x : Background m 2 Seed) : unitInterval × NonlowData (Seed:=Seed) k :=
  (conditionalMinimumSeed (nativeLowBidLaw Γ E) n
    (fun j => nativeBid (x.1 (e j))), (fun i => x.1 i,x.2))

lemma measurable_seedAndNonlow (Γ : FiniteGame m 2 c Seed) (E : Observable.Regions)
    (k : Fin m → Fin 4) (n : ℕ) (e : Fin (n+1) ≃ {i : Fin m // k i=0}) :
    Measurable (seedAndNonlow Γ E k n e) := by
  apply Measurable.prodMk
  · exact (measurable_conditionalMinimumSeed _ n).comp
      (measurable_pi_lambda _ fun j => measurable_nativeBid.comp
        ((measurable_pi_apply ((e j):Fin m)).comp measurable_fst))
  · have hc : Measurable (fun x : Background m 2 Seed =>
        fun i : {i : Fin m // k i ≠ 0} => x.1 i) :=
      measurable_pi_lambda _ (fun i => (measurable_pi_apply (i:Fin m)).comp
        (show Measurable (fun x : Background m 2 Seed => x.1) from measurable_fst))
    exact hc.prodMk measurable_snd

theorem native_seedAndNonlow_law (Γ : FiniteGame m 2 c Seed) (E : Observable.Regions)
    (k : Fin m → Fin 4)
    (hmass : ∀ i, (userLaw Γ) (E.coarseTag ⁻¹' {k i}) ≠ 0)
    (n : ℕ) (e : Fin (n+1) ≃ {i : Fin m // k i=0})
    (hLowBid : ∀ b, nativeLowBidLaw Γ E {b}=0) :
    (cond (backgroundLaw Γ) (categoryFiber E.coarseTag k ×ˢ univ)).map
      (seedAndNonlow Γ E k n e) =
        (volume : Measure unitInterval).prod (nonlowLaw Γ E k) :=
  native_background_minimum_seed Γ E.coarseTag E.measurable_coarseTag k 0
    hmass n e hLowBid

theorem positive_fiber_coordinate_masses (Γ : FiniteGame m 2 c Seed)
    (E : Observable.Regions) (k : Fin m → Fin 4)
    (h : (userProfileLaw Γ) (categoryFiber E.coarseTag k) ≠ 0) :
    ∀ i, (userLaw Γ) (E.coarseTag ⁻¹' {k i}) ≠ 0 := by
  rw [E.native_private_partition_mass Γ k] at h
  exact fun i => (Finset.prod_ne_zero_iff.mp h) i (Finset.mem_univ i)

variable {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω]
  [MeasurableSingletonClass Ω]

omit [Fintype Ω] [MeasurableSingletonClass Ω] in

theorem native_seed_sampled_joint (Γ : FiniteGame m 2 c Seed) (E : Observable.Regions)
    (k : Fin m → Fin 4)
    (hmass : ∀ i, (userLaw Γ) (E.coarseTag ⁻¹' {k i}) ≠ 0)
    (n : ℕ) (e : Fin (n+1) ≃ {i : Fin m // k i=0})
    (hLowBid : ∀ b, nativeLowBidLaw Γ E {b}=0)
    (f : NonlowData (Seed:=Seed) k → unitInterval → Ω)
    (hf : Measurable (Function.uncurry f)) :
    (cond (backgroundLaw Γ) (categoryFiber E.coarseTag k ×ˢ univ)).map
      (fun x => let z := seedAndNonlow Γ E k n e x
        (z.2,f z.2 z.1)) =
      ((nonlowLaw Γ E k).prod (volume : Measure unitInterval)).map
        (fun z => (z.1,f z.1 z.2)) := by
  letI (i : {i : Fin m // k i ≠ 0}) :
      IsProbabilityMeasure (cond (userLaw Γ) (E.coarseTag ⁻¹' {k i})) :=
    cond_isProbabilityMeasure (hmass i)
  letI : IsProbabilityMeasure (nonlowLaw Γ E k) := by
    unfold nonlowLaw
    infer_instance
  let h : NonlowData (Seed:=Seed) k × unitInterval → NonlowData (Seed:=Seed) k × Ω :=
    fun z => (z.1,f z.1 z.2)
  have hh : Measurable h := measurable_fst.prodMk hf
  have hswap :
      ((volume : Measure unitInterval).prod (nonlowLaw Γ E k)).map Prod.swap =
        (nonlowLaw Γ E k).prod (volume : Measure unitInterval) :=
    (Measure.measurePreserving_swap (μ := (volume : Measure unitInterval))
      (ν := nonlowLaw Γ E k)).map_eq
  calc
    _ = (((cond (backgroundLaw Γ) (categoryFiber E.coarseTag k ×ˢ univ)).map
        (seedAndNonlow Γ E k n e)).map Prod.swap).map h := by
      rw [Measure.map_map hh measurable_swap,
        Measure.map_map (hh.comp measurable_swap) (measurable_seedAndNonlow Γ E k n e)]
      rfl
    _ = _ := by rw [native_seedAndNonlow_law Γ E k hmass n e hLowBid,hswap]

theorem native_seed_probability (Γ : FiniteGame m 2 c Seed) (E : Observable.Regions)
    (k : Fin m → Fin 4)
    (hmass : ∀ i, (userLaw Γ) (E.coarseTag ⁻¹' {k i}) ≠ 0)
    (n : ℕ) (e : Fin (n+1) ≃ {i : Fin m // k i=0})
    (hLowBid : ∀ b, nativeLowBidLaw Γ E {b}=0)
    (C : NonlowData (Seed:=Seed) k → FiniteLaw Ω)
    (f : NonlowData (Seed:=Seed) k → unitInterval → Ω)
    (hf : Measurable (Function.uncurry f))
    (hlaw : ∀ x, volume.map (f x) = FiniteLaw.probabilityMeasure (C x))
    (P : NonlowData (Seed:=Seed) k → Ω → Prop)
    (hP : MeasurableSet {z : NonlowData (Seed:=Seed) k × Ω | P z.1 z.2}) :
    (cond (backgroundLaw Γ) (categoryFiber E.coarseTag k ×ˢ univ)).real
      {x | let z := seedAndNonlow Γ E k n e x
        P z.2 (f z.2 z.1)} =
      ∫ x, (C x).prob (P x) ∂nonlowLaw Γ E k := by
  letI (i : {i : Fin m // k i ≠ 0}) :
      IsProbabilityMeasure (cond (userLaw Γ) (E.coarseTag ⁻¹' {k i})) :=
    cond_isProbabilityMeasure (hmass i)
  letI : IsProbabilityMeasure (nonlowLaw Γ E k) := by
    unfold nonlowLaw
    infer_instance
  have hsource : Measurable (fun x : Background m 2 Seed =>
      let z := seedAndNonlow Γ E k n e x
      (z.2,f z.2 z.1)) :=
    (measurable_snd.prodMk (hf.comp (measurable_snd.prodMk measurable_fst))).comp
      (measurable_seedAndNonlow Γ E k n e)
  have hout : Measurable (fun z : NonlowData (Seed:=Seed) k × unitInterval =>
      (z.1,f z.1 z.2)) := measurable_fst.prodMk hf
  have he := congrArg
    (fun ν : Measure (NonlowData (Seed:=Seed) k × Ω) => ν {z | P z.1 z.2})
    (native_seed_sampled_joint Γ E k hmass n e hLowBid f hf)
  rw [Measure.map_apply hsource hP,Measure.map_apply hout hP] at he
  have heR := congrArg ENNReal.toReal he
  have hsame : (cond (backgroundLaw Γ) (categoryFiber E.coarseTag k ×ˢ univ)).real
      {x | let z := seedAndNonlow Γ E k n e x; P z.2 (f z.2 z.1)} =
      ((nonlowLaw Γ E k).prod (volume : Measure unitInterval)).real
        {z | P z.1 (f z.1 z.2)} := by
    simpa only [measureReal_def,Set.preimage,Set.mem_setOf_eq] using heR
  exact hsame.trans (sampler_probability_integral (nonlowLaw Γ E k) C f hf hlaw P hP)

end NativeConditionalSeed

end FCAppendix.Affine.Tail04.NativeFlag
