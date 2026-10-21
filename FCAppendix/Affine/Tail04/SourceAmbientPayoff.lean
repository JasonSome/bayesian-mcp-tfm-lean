import FCAppendix.Affine.Tail04.SourceNoiseIntegration

noncomputable section
namespace FCAppendix.Affine.Tail04.SourceAmbientPayoff
open MeasureTheory ProbabilityTheory Set Classical
open Existence.Distributional EqualPrivateSignal CompactSourceBidLaws FixedAmbientNoise
open FiniteTailNoisyGame SourceTailNoisyFixedPoint SourceAmbientLaws AmbientFiniteGame
open EqualPrivateAmbient SourceBoxCoherence
open BoundedProbabilityIntegral (measurable_integral)
open scoped BigOperators

variable (D : Data) (A H0 H1 : ℕ) (reg low : Bool)
  (e : Noise D.eps) (he : 0<(e:ℝ)) (hes : (e:ℝ)< D.eps)
  (μP : ProbabilityMeasure (Icc D.R D.Up)) (μA : ProbabilityMeasure (Icc (1:ℝ) D.U))

private lemma widen_cons {N : ℕ} {L B C : ℝ} (h : B≤C)
    (p : Icc L B) (b : Fin N→Icc L B) :
    Fin.cons (widen h p) (fun i=>widen h (b i))=
      fun i=>widen h ((Fin.cons p b : Fin (N+1)→Icc L B) i) := by
  funext i
  exact Fin.cases rfl (fun _=>rfl) i

theorem active_value_positive (v : ℝ) (price : Icc (1:ℝ) D.U)
    (b : Fin A→ Icc (1:ℝ) (D.U*(1+(e:ℝ)))) (u : unitInterval) :
    activeValue D A H0 H1 reg low e μP v price
      (fun i=> widen (upper_mono (by norm_num) D.hU e) (b i)) u=
    ActivePhysicalPayoff.value (atNoise D e he hes) A H0 H1 μP v reg low
      (Fin.cons (noisyBid (by norm_num) he.le (price,u)) b) := by
  let hB := upper_mono (by norm_num) D.hU e
  let hV := upper_mono D.hR D.hRUp e
  let row : Fin (A+1)→Icc (1:ℝ) (D.U*(1+(e:ℝ))) :=
    Fin.cons (noisyBid (by norm_num) he.le (price,u)) b
  let prior := WeakProbability.mk ((atNoise D e he hes).privateBayes H0 μP)
  have hrow : Fin.cons (physical (by norm_num) D.hU (e,price,u))
      (fun i=>widen hB (b i))=(fun i=>widen hB (row i)) :=
    widen_cons hB (noisyBid (by norm_num) he.le (price,u)) b
  have hc : activeCount D A H0 H1 reg low e μP v price
      (fun i=>widen hB (b i)) u=
      AllCountActiveFiniteGain.physicalCount H0 H1 D.c D.ξ (D.U*(1+(e:ℝ))) D.R
        (D.Up*(1+(e:ℝ))) D.width (D.e0 reg) D.F reg low
        (D.marksLaw H0) (D.marksLaw H1) ((atNoise D e he hes).privateBayes H0 μP) row 0 := by
    unfold activeCount AllCountActiveFiniteGain.physicalCount
    by_cases h : H0=H1
    · rw [if_pos h,if_pos h,SourceAmbientLaws.bayes_positive D H0 e he hes μP]
      exact (congrArg (fun r : Fin (A+1)→Icc (1:ℝ) D.B=>
        EqualPrivateCountPayoff.countLaw (A+1) H0 D.c D.R D.V D.ξ 1 D.B
          (r,law hV prior) 0) hrow).trans
        (equal_count_sorted_widen hV hB D.hξ row prior 0)
    · rw [if_neg h,if_neg h]
      have hr : (fun i=>((Fin.cons (physical (by norm_num) D.hU (e,price,u))
          (fun j=>widen hB (b j)) : Fin (A+1)→Icc (1:ℝ) D.B) i:ℝ))=(fun i=>(row i:ℝ)) := by
        funext i
        exact Fin.cases rfl (fun _=>rfl) i
      exact congrArg (fun r : Fin (A+1)→ℝ=>
        UnequalNoisyCountPayoff.rawCount H0 H1 D.c D.ξ (D.U*(1+(e:ℝ))) D.R
          (D.Up*(1+(e:ℝ))) D.width (D.e0 reg) D.F reg low
          (D.marksLaw H0) (D.marksLaw H1) r 0) hr
  convert! congrArg (fun q : CountLaw 2=>affineCountUtility q v
    (Hybrid.activeNoisyRealBid e price u) D.eta D.heta0 D.heta1) hc using 1

theorem active_positive (v : ℝ) (price : Icc (1:ℝ) D.U) :
    active D A H0 H1 reg low e μP μA v price=
      ∫b,(atNoise D e he hes).activeFiber A H0 H1 low reg ((v,price,μP),b)
        ∂(rowLaw A μA : Measure (Fin A→Icc (1:ℝ) D.U)) := by
  have hmeas:=measurable_activeValue D A H0 H1 reg low e μP v price
  unfold active
  rw [SourceAmbientLaws.common_positive D e he hes μA]
  erw [SourceNoiseIntegration.widen_row A _ _ _ (measurable_integral volume _ hmeas)]
  simp_rw [active_value_positive D A H0 H1 reg low e he hes μP]
  erw [SourceNoiseIntegration.focal A (by norm_num) he.le μA price
    (ActivePhysicalPayoff.value (atNoise D e he hes) A H0 H1 μP v reg low)
    (ActivePhysicalPayoff.measurable_value (atNoise D e he hes) A H0 H1 μP v reg low)
    (ActivePhysicalPayoff.value_bound (atNoise D e he hes) A H0 H1 μP v reg low)]
  apply integral_congr_ae
  exact ae_of_all _ fun b=>
    (ActivePhysicalPayoff.activeFiber_integral (atNoise D e he hes) A H0 H1 μP v low reg price b).symm

theorem active_value_zero (v : ℝ) (price : Icc (1:ℝ) D.U)
    (b : Fin A→ Icc (1:ℝ) D.U) (u : unitInterval) :
    activeValue D A H0 H1 reg low (zero D.eps D.heps.le) μP v price
      (fun i=> widen (base_le_upper (by norm_num) D.hU D.heps.le) (b i)) u=
    ZeroNoiseFiniteGame.activeFiber D A H0 H1 low reg ((v,price,μP),b) := by
  let hB := base_le_upper (by norm_num) D.hU D.heps.le
  let hV := base_le_upper D.hR D.hRUp D.heps.le
  have hrow : Fin.cons (physical (by norm_num) D.hU (zero D.eps D.heps.le,price,u))
      (fun i=>widen hB (b i))=(fun i=>widen hB ((Fin.cons price b : Fin (A+1)→Icc (1:ℝ) D.U) i)) := by
    simpa only [physical_zero] using widen_cons hB price b
  have hc : activeCount D A H0 H1 reg low (zero D.eps D.heps.le) μP v price
      (fun i=>widen hB (b i)) u=
    if H0=H1 then
      EqualPrivateCountPayoff.countLaw (A+1) H0 D.c D.R D.Up D.ξ 1 D.U
        (Fin.cons price b,ZeroNoiseFiniteGame.privateBayes D H0 μP) 0
    else UnequalNoisyCountPayoff.rawCount H0 H1 D.c D.ξ D.U D.R D.Up D.width
      (D.e0 reg) D.F reg low (D.marksLaw H0) (D.marksLaw H1)
      (fun i=>((Fin.cons price b : Fin (A+1)→Icc (1:ℝ) D.U) i:ℝ)) 0 := by
    unfold activeCount
    by_cases h : H0=H1
    · rw [if_pos h,if_pos h,SourceAmbientLaws.bayes_zero D H0 μP]
      exact (congrArg (fun r : Fin (A+1)→Icc (1:ℝ) D.B=>
        EqualPrivateCountPayoff.countLaw (A+1) H0 D.c D.R D.V D.ξ 1 D.B
          (r,law hV (ZeroNoiseFiniteGame.privateBayes D H0 μP)) 0) hrow).trans
        (activeCount_widen hV hB D.hξ (Fin.cons price b)
          (ZeroNoiseFiniteGame.privateBayes D H0 μP) 0)
    · simp only [if_neg h,zero,add_zero,mul_one]
      have hr : (fun i=>((Fin.cons
          (physical (by norm_num) D.hU (zero D.eps D.heps.le,price,u))
          (fun j=>widen hB (b j)) : Fin (A+1)→Icc (1:ℝ) D.B) i:ℝ))=
          (fun i=>((Fin.cons price b : Fin (A+1)→Icc (1:ℝ) D.U) i:ℝ)) := by
        funext i
        refine Fin.cases ?_ (fun _=>rfl) i
        simp only [Fin.cons_zero,physical_value,zero,zero_mul,add_zero,mul_one]
      exact congrArg (fun r : Fin (A+1)→ℝ=>
        UnequalNoisyCountPayoff.rawCount H0 H1 D.c D.ξ D.U D.R D.Up D.width
          (D.e0 reg) D.F reg low (D.marksLaw H0) (D.marksLaw H1) r 0) hr
  have hh := congrArg (fun q : CountLaw 2=>affineCountUtility q v
    (price:ℝ) D.eta D.heta0 D.heta1) hc
  by_cases h : H0=H1
  · rw [if_pos h] at hh
    simpa only [activeValue,physical_value,zero,zero_mul,add_zero,mul_one,
      ZeroNoiseFiniteGame.activeFiber,if_pos h,Data.insertActive,EqualPrivateCountPayoff.utility,
      Fin.cons_zero] using! hh
  · rw [if_neg h] at hh
    simpa only [activeValue,physical_value,zero,zero_mul,add_zero,mul_one,
      ZeroNoiseFiniteGame.activeFiber,if_neg h,Data.insertActive] using! hh

theorem active_zero (v : ℝ) (price : Icc (1:ℝ) D.U) :
    active D A H0 H1 reg low (zero D.eps D.heps.le) μP μA v price=
      ∫b,ZeroNoiseFiniteGame.activeFiber D A H0 H1 low reg ((v,price,μP),b)
        ∂(rowLaw A μA : Measure (Fin A→Icc (1:ℝ) D.U)) := by
  have hmeas:=measurable_activeValue D A H0 H1 reg low (zero D.eps D.heps.le) μP v price
  unfold active
  rw [SourceAmbientLaws.common_zero D μA]
  erw [SourceNoiseIntegration.widen_row A _ _ _ (measurable_integral volume _ hmeas)]
  simp_rw [active_value_zero D A H0 H1 reg low μP]
  simp

theorem equal_value_positive (H : ℕ) (j : Fin H) (v : ℝ) (price : Icc D.R D.Up)
    (b : Fin A→ Icc (1:ℝ) (D.U*(1+(e:ℝ))))
    (s : Signal H D.R (D.Up*(1+(e:ℝ)))) (u : unitInterval) :
    equalPrivateValue D A H j e μP v price
      (fun i=> widen (upper_mono (by norm_num) D.hU e) (b i))
      (signal (upper_mono D.hR D.hRUp e) s) u=
    (v-Hybrid.activeNoisyRealBid e price u)*
      PrivatePayoffContinuity.privateValue (c:=D.c) D.ξ j
        (fun i=>(SortedAllNoise.sortedBox b i:ℝ),
          policyMean A H D.c D.R (D.Up*(1+(e:ℝ))) D.ξ 1 (D.U*(1+(e:ℝ)))
            (SortedAllNoise.sortedBox b,WeakProbability.mk ((atNoise D e he hes).privateBayes H μP)),
          Function.update s j (Sum.inr (noisyBid D.hR he.le (price,u)))) := by
  have hh := congrArg (fun x : ℝ=>(v-Hybrid.activeNoisyRealBid e price u)*x)
    (privateValue_widen (c:=D.c) (R:=D.R) (upper_mono D.hR D.hRUp e)
      (upper_mono (by norm_num) D.hU e) D.hξ b
      (WeakProbability.mk ((atNoise D e he hes).privateBayes H μP)) s j
      (noisyBid D.hR he.le (price,u)))
  unfold equalPrivateValue
  rw [SourceAmbientLaws.bayes_positive D H e he hes μP]
  dsimp only [physical]
  exact hh

theorem equal_value_zero (H : ℕ) (j : Fin H) (v : ℝ) (price : Icc D.R D.Up)
    (b : Fin A→ Icc (1:ℝ) D.U) (s : Signal H D.R D.Up) (u : unitInterval) :
    equalPrivateValue D A H j (zero D.eps D.heps.le) μP v price
      (fun i=> widen (base_le_upper (by norm_num) D.hU D.heps.le) (b i))
      (signal (base_le_upper D.hR D.hRUp D.heps.le) s) u=
    (v-(price:ℝ))*ZeroNoiseFiniteGame.equalPartialValue D A H j b μP price s := by
  have hh := congrArg (fun x : ℝ=>(v-(price:ℝ))*x)
    (privateValue_widen (c:=D.c) (R:=D.R) (base_le_upper D.hR D.hRUp D.heps.le)
      (base_le_upper (by norm_num) D.hU D.heps.le) D.hξ b
      (ZeroNoiseFiniteGame.privateBayes D H μP) s j price)
  unfold equalPrivateValue
  rw [SourceAmbientLaws.bayes_zero D H μP,physical_zero]
  exact hh

theorem unequal_value_positive (side : Bool) (j : Fin (AllCountAtypical.ownCount H0 H1 side))
    (v : ℝ) (price : Icc D.R D.Up) (b : Fin A→ Icc (1:ℝ) (D.U*(1+(e:ℝ))))
    (s : Signal (AllCountAtypical.ownCount H0 H1 side) D.R (D.Up*(1+(e:ℝ))))
    (u : unitInterval) :
    unequalPrivateValue D A H0 H1 side reg low j e v price
      (fun i=> widen (upper_mono (by norm_num) D.hU e) (b i))
      (signal (upper_mono D.hR D.hRUp e) s) u=
    (v-Hybrid.activeNoisyRealBid e price u)*
      (UnequalPartialCountPayoff.rawWeight A H0 H1 D.c D.ξ (D.U*(1+(e:ℝ))) D.R
        (D.Up*(1+(e:ℝ))) D.width (D.e0 reg) D.F reg low (D.marksLaw H0) (D.marksLaw H1)
        (fun i=>(b i:ℝ))*(if reg then 0 else 1)+
      (1-UnequalPartialCountPayoff.rawWeight A H0 H1 D.c D.ξ (D.U*(1+(e:ℝ))) D.R
        (D.Up*(1+(e:ℝ))) D.width (D.e0 reg) D.F reg low (D.marksLaw H0) (D.marksLaw H1)
        (fun i=>(b i:ℝ)))*AtypicalPartialNoisy.rankInclusion A H0 H1 D.c side j
          (Hybrid.activeNoisyRealBid e price u,s)) := by
  let w:=UnequalPartialCountPayoff.rawWeight A H0 H1 D.c D.ξ (D.U*(1+(e:ℝ))) D.R
    (D.Up*(1+(e:ℝ))) D.width (D.e0 reg) D.F reg low (D.marksLaw H0) (D.marksLaw H1)
    (fun i=>(b i:ℝ))
  have hh := congrArg (fun x : ℝ=>(v-Hybrid.activeNoisyRealBid e price u)*
      (w*(if reg then 0 else 1)+(1-w)*x))
    (rankInclusion_widen A H0 H1 D.c (upper_mono D.hR D.hRUp e) side j
      (Hybrid.activeNoisyRealBid e price u) s)
  convert! hh using 1

theorem unequal_value_zero (side : Bool) (j : Fin (AllCountAtypical.ownCount H0 H1 side))
    (v : ℝ) (price : Icc D.R D.Up) (b : Fin A→ Icc (1:ℝ) D.U)
    (s : Signal (AllCountAtypical.ownCount H0 H1 side) D.R D.Up) (u : unitInterval) :
    unequalPrivateValue D A H0 H1 side reg low j (zero D.eps D.heps.le) v price
      (fun i=> widen (base_le_upper (by norm_num) D.hU D.heps.le) (b i))
      (signal (base_le_upper D.hR D.hRUp D.heps.le) s) u=
    (v-(price:ℝ))*
      (UnequalPartialCountPayoff.rawWeight A H0 H1 D.c D.ξ D.U D.R D.Up D.width (D.e0 reg) D.F
        reg low (D.marksLaw H0) (D.marksLaw H1) (fun i=>(b i:ℝ))*(if reg then 0 else 1)+
      (1-UnequalPartialCountPayoff.rawWeight A H0 H1 D.c D.ξ D.U D.R D.Up D.width (D.e0 reg) D.F
        reg low (D.marksLaw H0) (D.marksLaw H1) (fun i=>(b i:ℝ)))*
        AtypicalPartialNoisy.rankInclusion A H0 H1 D.c side j ((price:ℝ),s)) := by
  let w:=UnequalPartialCountPayoff.rawWeight A H0 H1 D.c D.ξ D.U D.R D.Up D.width
    (D.e0 reg) D.F reg low (D.marksLaw H0) (D.marksLaw H1) (fun i=>(b i:ℝ))
  have hh := congrArg (fun x : ℝ=>(v-(price:ℝ))*
      (w*(if reg then 0 else 1)+(1-w)*x))
    (rankInclusion_widen A H0 H1 D.c (base_le_upper D.hR D.hRUp D.heps.le) side j
      (price:ℝ) s)
  simpa only [unequalPrivateValue,physical_value,zero,zero_mul,add_zero,mul_one,widen,w]
    using! hh

end FCAppendix.Affine.Tail04.SourceAmbientPayoff
