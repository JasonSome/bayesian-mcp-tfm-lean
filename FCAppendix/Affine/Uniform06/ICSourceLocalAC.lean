import FCAppendix.Affine.Uniform06.ICAbsorption

noncomputable section
namespace FCAppendix.Affine.Uniform06.ICAbsorption

open MeasureTheory Set Filter Topology
open Rank ScaledMeasure

theorem continuous_le_on_closed_support
    (μ : Measure ℝ) (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g)
    (hfg : ∀ᵐ x ∂μ, f x ≤ g x) :
    ∀ x ∈ μ.support, f x ≤ g x := by
  intro x hx
  by_contra hbad
  have hopen : IsOpen {y | g y < f y} := isOpen_lt hg hf
  have hnear : {y | g y < f y} ∈ 𝓝 x :=
    hopen.mem_nhds (lt_of_not_ge hbad)
  have hmass := (Measure.mem_support_iff_forall x).mp hx _ hnear
  have hzero : μ {y | g y < f y}=0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hfg] with y hy
    exact not_lt_of_ge hy
  rw [hzero] at hmass
  exact (lt_irrefl 0) hmass

theorem finite_IC_compact_Borel_contraction
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hatom : ∀ x : ℝ, μ {x}=0)
    (M ℓ cap S D : ℝ → ℝ) (η κ r A B L W hi δS : ℝ)
    (hM : Continuous M) (hℓ : Continuous ℓ) (hcap : Continuous cap)
    (hScont : ContinuousOn S (Ioi 0)) (hDcont : ContinuousOn D (Ioi 0))
    (hIC : ∀ᵐ b ∂μ, 0 < b → ∀ a : ℝ, 0 < a → ℓ (M b) < a → a < cap (M b) →
      payoff η (M b) a (S a) (D a) ≤ payoff η (M b) b (S b) (D b))
    (hfloor : ∀ᵐ b ∂μ, ℓ (M b) ≤ b)
    (hcapLegal : ∀ v b : ℝ, b < v → b ≤ hi → b < cap v)
    (hη : 0 ≤ η) (hκ : 0 < κ) (hr : 0 < r) (hA : 0 < A)
    (hB : 0 ≤ B) (hL : 0 ≤ L) (hW : 0 ≤ W) (hδS : 0 < δS)
    (hsmall : 8*η*B < r*A)
    (hrent : ∀ a ∈ μ.support, a ∈ Ioc 0 hi → r*a ≤ M a-a)
    (hlevel : ∀ a ∈ Ioc 0 hi, S a+η*D a ≤ W)
    (hfirst : ∀ a b : ℝ, 0 < a → a < b → b ≤ hi → b-a ≤ δS →
      A*μ.real (Ioc a b) ≤ S b-S a)
    (hdup : ∀ a b : ℝ, 0 < a → a < b → b ≤ hi →
      D b-D a ≤ B*(μ.real (Ioc a b)+μ.real (Ioc (κ*a) (κ*b)))+
        L*(b-a)/a)
    {lo : ℝ} (hlo : 0 < lo) :
    ∀ E : Set ℝ, MeasurableSet E → E ⊆ Ioc lo hi →
      μ.real E ≤
        ((W+2*η*L)/(lo*(r*A/2-2*η*B)))*volume.real E+
        (2*η*B/(r*A/2-2*η*B))*μ.real (scaledSet κ E) := by
  let d := r*A/2-2*η*B
  let ε := 2*η*B/d
  let C := (W+2*η*L)/(lo*d)
  let δ := min δS (min lo (r*lo/2))
  obtain ⟨hd,hε0,hε1⟩ := absorption_coefficient_bounds hη hr hA hB hsmall
  have hC : 0 ≤ C := by dsimp [C,d]; positivity
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hfloorS := continuous_le_on_closed_support μ (fun b => ℓ (M b)) id
    (hℓ.comp hM) continuous_id hfloor
  apply Borel_contraction_of_anchored_intervals μ hatom hκ hC hε0 hδ
  intro a ha b haI hbI hab hstep
  by_cases heq : a=b
  · subst b
    simp only [Ioc_self,measureReal_empty,sub_self,mul_zero,zero_add]
    positivity
  have hab' : a < b := lt_of_le_of_ne hab heq
  have ha0 : 0 < a := hlo.trans_le haI.1
  have haHi : a ∈ Ioc 0 hi := ⟨ha0,haI.2⟩
  have hrenta := hrent a ha haHi
  have hsS : b-a ≤ δS := hstep.trans (min_le_left _ _)
  have hslo : b-a ≤ lo :=
    hstep.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hsr : b-a ≤ r*lo/2 :=
    hstep.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hhalf : b-a ≤ r*a/2 := hsr.trans (by nlinarith [haI.1])
  have hb2 : b ≤ 2*a := by linarith [haI.1]
  have hlegalL : ℓ (M a) < b := (hfloorS a ha).trans_lt hab'
  have hlegalU : b < cap (M a) := by
    have hpositive : 0 < r*a/2 := by positivity
    have hbM : b < M a := by linarith
    exact hcapLegal (M a) b hbM hbI.2
  have hic := IC_on_closed_used_support μ M ℓ cap S D η
    hM hℓ hcap hScont hDcont hIC a ha ha0 b
    (ha0.trans hab') hlegalL hlegalU
  have hh := finite_IC_absorb hη hr hA hB hL hW ha0 hab hb2 hhalf hrenta
    (measureReal_nonneg : 0 ≤ μ.real (Ioc a b))
    (measureReal_nonneg : 0 ≤ μ.real (Ioc (κ*a) (κ*b)))
    hic (hfirst a b ha0 hab' hbI.2 hsS)
    (hdup a b ha0 hab' hbI.2) (hlevel a haHi) hd
  have hcoeff : (W+2*η*L)/(a*d) ≤ C := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    dsimp only [d]
    exact mul_le_mul_of_nonneg_right haI.1 hd.le
  have hbound := mul_le_mul_of_nonneg_right hcoeff (sub_nonneg.mpr hab)
  exact hh.trans (by linarith)

theorem finite_IC_local_rank_ac
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hatom : ∀ x : ℝ, μ {x}=0)
    (M ℓ cap S D : ℝ → ℝ) (η κ r A B L W hi δS : ℝ)
    (hM : Continuous M) (hℓ : Continuous ℓ) (hcap : Continuous cap)
    (hScont : ContinuousOn S (Ioi 0)) (hDcont : ContinuousOn D (Ioi 0))
    (hIC : ∀ᵐ b ∂μ, 0 < b → ∀ a : ℝ, 0 < a → ℓ (M b) < a → a < cap (M b) →
      payoff η (M b) a (S a) (D a) ≤ payoff η (M b) b (S b) (D b))
    (hfloor : ∀ᵐ b ∂μ, ℓ (M b) ≤ b)
    (hcapLegal : ∀ v b : ℝ, b < v → b ≤ hi → b < cap v)
    (hη : 0 ≤ η) (hκ : 0 < κ) (hκ1 : κ < 1)
    (hr : 0 < r) (hA : 0 < A) (hB : 0 ≤ B) (hL : 0 ≤ L) (hW : 0 ≤ W)
    (hδS : 0 < δS) (hsmall : 8*η*B < r*A)
    (hrent : ∀ a ∈ μ.support, a ∈ Ioc 0 hi → r*a ≤ M a-a)
    (hlevel : ∀ a ∈ Ioc 0 hi, S a+η*D a ≤ W)
    (hfirst : ∀ a b : ℝ, 0 < a → a < b → b ≤ hi → b-a ≤ δS →
      A*μ.real (Ioc a b) ≤ S b-S a)
    (hdup : ∀ a b : ℝ, 0 < a → a < b → b ≤ hi →
      D b-D a ≤ B*(μ.real (Ioc a b)+μ.real (Ioc (κ*a) (κ*b)))+
        L*(b-a)/a) :
    μ.restrict (Ioc 0 hi) ≪ volume := by
  let ε := 2*η*B/(r*A/2-2*η*B)
  obtain ⟨hd,hε0,hε1⟩ := absorption_coefficient_bounds hη hr hA hB hsmall
  apply local_ac_of_compact_null_contraction μ hκ hκ1.le hε0 hε1
  intro lo hlo E hEm hE hnull
  have hh := finite_IC_compact_Borel_contraction μ hatom M ℓ cap S D η κ r A B L W hi δS
    hM hℓ hcap hScont hDcont hIC hfloor hcapLegal hη hκ hr hA hB hL hW hδS hsmall
    hrent hlevel hfirst hdup hlo E hEm hE
  have hz : volume.real E=0 := by simp only [Measure.real,hnull,ENNReal.toReal_zero]
  simpa only [hz,mul_zero,zero_add] using hh

theorem min_cap_upward_legal {hi U : ℝ} (hU : hi < U) :
    ∀ v b : ℝ, b < v → b ≤ hi → b < min v U := by
  intro v b hbv hbhi
  exact lt_min hbv (hbhi.trans_lt hU)

end FCAppendix.Affine.Uniform06.ICAbsorption
