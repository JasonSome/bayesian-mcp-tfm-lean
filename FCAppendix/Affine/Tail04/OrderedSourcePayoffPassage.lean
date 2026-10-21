import FCAppendix.Affine.Tail04.OrderedSourcePayoffExpansion

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedSourcePayoffPassage
open MeasureTheory ProbabilityTheory Set Filter Topology Classical Hybrid
open Existence.Distributional OriginalValues EqualPrivateSignal CompactSourceBidLaws
open FiniteTailNoisyGame SourceTailNoisyFixedPoint OrderedOriginalNoisySequence
open OrderedSourceFinitePayoffTests OrderedSourceAmbientSequence OrderedSourceFiberIntegrals OrderedSourcePayoffExpansion
open scoped BigOperators

variable (D : Data) (P : ValueParameters) (t : ℝ) (ht : P.M< t) (N : ℕ)
  (S : Sequence D P t ht N)
  [NullSingletonClass ((ProbabilityMeasure.toMeasure (S.limit 0).1).map (fun x=>(x.2:ℝ)))]
  [NullSingletonClass ((ProbabilityMeasure.toMeasure (S.limit 1).1).map (fun x=>(x.2:ℝ)))]
  [NullSingletonClass ((ProbabilityMeasure.toMeasure (S.limit 2).1).map (fun x=>(x.2:ℝ)))]

local notation "Ds"=> installOriginal D P t ht
local notation "Dn" n=> installOriginal (S.data n) P t ht
local notation "μP" π=> partialLaw D P t ht π
local notation "μA" π=> commonLaw D P t ht π
local notation "μn" => (fun (n : ℕ) (k : Fin 3) => ProbabilityMeasure.toMeasure (Subtype.val (S.law n k)))
local notation "μz" => (fun k : Fin 3 => ProbabilityMeasure.toMeasure (Subtype.val (S.limit k)))

omit [NullSingletonClass ((ProbabilityMeasure.toMeasure (S.limit 0).1).map (fun x=>(x.2:ℝ)))] [NullSingletonClass ((ProbabilityMeasure.toMeasure (S.limit 1).1).map (fun x=>(x.2:ℝ)))] [NullSingletonClass ((ProbabilityMeasure.toMeasure (S.limit 2).1).map (fun x=>(x.2:ℝ)))] in
lemma continuous_noisy_active (k : Fin 3) (A H0 H1 : ℕ) (reg low : Bool)
    (action : C(Own D P t k,Icc (1:ℝ) D.U)) (n : ℕ) :
    Continuous (fun x=> active (Dn n) A H0 H1 reg low (μP (S.law n)) (μA (S.law n))
      (x.1:ℝ) (action x)) :=
  (continuous_active (Dn n) A H0 H1 reg low _ _).comp
    ((value D P t k).continuous.prodMk action.continuous)

omit [NullSingletonClass ((ProbabilityMeasure.toMeasure (S.limit 0).1).map (fun x=>(x.2:ℝ)))] [NullSingletonClass ((ProbabilityMeasure.toMeasure (S.limit 1).1).map (fun x=>(x.2:ℝ)))] [NullSingletonClass ((ProbabilityMeasure.toMeasure (S.limit 2).1).map (fun x=>(x.2:ℝ)))] in
lemma continuous_noisy_partial (A H0 H1 : ℕ) (side reg low : Bool)
    (j : Fin (AllCountAtypical.ownCount H0 H1 side))
    (action : C(Own D P t 2,Icc D.R D.Up)) (n : ℕ) :
    Continuous (fun x=> «partial» (Dn n) A H0 H1 side reg low j (μP (S.law n)) (μA (S.law n))
      (x.1:ℝ) (action x)) :=
  (continuous_partial (Dn n) A H0 H1 side reg low j _ _).comp
    ((value D P t 2).continuous.prodMk action.continuous)

omit [NullSingletonClass ((ProbabilityMeasure.toMeasure (S.limit 2).1).map (fun x=>(x.2:ℝ)))] in
lemma active_mix (k : Fin 3) (A H0 H1 : ℕ) (low : Bool)
    (action : C(Own D P t k,Icc (1:ℝ) D.U)) (a : C(Own D P t k,ℝ)) :
    Tendsto (fun n=>∫x,a x*activeMix (Dn n) A H0 H1 low (μP (S.law n)) (μA (S.law n))
      (x.1:ℝ) (action x) ∂ μn n k) atTop
      (𝓝 (∫x,a x*zeroActiveMix Ds A H0 H1 low (μP S.limit) (μA S.limit)
        (x.1:ℝ) (action x) ∂ μz k)) := by
  have hn (n : ℕ) (reg : Bool) := FinitePayoffLinearity.continuous_integrable (μn n k) _
    (a.continuous.mul (continuous_noisy_active D P t ht N S k A H0 H1 reg low action n))
  have hz (reg : Bool) := FinitePayoffLinearity.continuous_integrable (μz k) _
    (a.continuous.mul (continuous_zero_active D P t ht N S k A H0 H1 reg low action))
  have h0:=OrderedSourceFinitePayoffTests.active_fiber D P t ht N S k A H0 H1 false low action a
  have h1:=OrderedSourceFinitePayoffTests.active_fiber D P t ht N S k A H0 H1 true low action a
  have hh:=(h0.const_mul (1-(D.regimeShare:ℝ))).add (h1.const_mul (D.regimeShare:ℝ))
  convert! hh using 1
  · funext n
    exact FinitePayoffLinearity.test_mix (μn n k) a
      (fun x=>active (Dn n) A H0 H1 false low (μP (S.law n)) (μA (S.law n)) (x.1:ℝ) (action x))
      (fun x=>active (Dn n) A H0 H1 true low (μP (S.law n)) (μA (S.law n)) (x.1:ℝ) (action x))
      (1-(D.regimeShare:ℝ)) (D.regimeShare:ℝ) (hn n false) (hn n true)
  · exact congrArg (fun y : ℝ=>𝓝 y) (FinitePayoffLinearity.test_mix (μz k) a
      (fun x=>zeroActive Ds A H0 H1 false low (μP S.limit) (μA S.limit) (x.1:ℝ) (action x))
      (fun x=>zeroActive Ds A H0 H1 true low (μP S.limit) (μA S.limit) (x.1:ℝ) (action x))
      (1-(D.regimeShare:ℝ)) (D.regimeShare:ℝ) (hz false) (hz true))

lemma partial_mix (A H0 H1 : ℕ) (side low : Bool)
    (j : Fin (AllCountAtypical.ownCount H0 H1 side))
    (action : C(Own D P t 2,Icc D.R D.Up)) (a : C(Own D P t 2,ℝ)) :
    Tendsto (fun n=>∫x,a x*partialMix (Dn n) A H0 H1 side low j (μP (S.law n)) (μA (S.law n))
      (x.1:ℝ) (action x) ∂ μn n 2) atTop
      (𝓝 (∫x,a x*zeroPartialMix Ds A H0 H1 side low j (μP S.limit) (μA S.limit)
        (x.1:ℝ) (action x) ∂ μz 2)) := by
  have hn (n : ℕ) (reg : Bool) := FinitePayoffLinearity.continuous_integrable (μn n 2) _
    (a.continuous.mul (continuous_noisy_partial D P t ht N S A H0 H1 side reg low j action n))
  have hz (reg : Bool) := FinitePayoffLinearity.continuous_integrable (μz 2) _
    (a.continuous.mul (continuous_zero_partial D P t ht N S A H0 H1 side reg low j action))
  have h0:=OrderedSourceFinitePayoffTests.partial_fiber D P t ht N S A H0 H1 side false low j action a
  have h1:=OrderedSourceFinitePayoffTests.partial_fiber D P t ht N S A H0 H1 side true low j action a
  have hh:=(h0.const_mul (1-(D.regimeShare:ℝ))).add (h1.const_mul (D.regimeShare:ℝ))
  convert! hh using 1
  · funext n
    exact FinitePayoffLinearity.test_mix (μn n 2) a
      (fun x=>«partial» (Dn n) A H0 H1 side false low j (μP (S.law n)) (μA (S.law n)) (x.1:ℝ) (action x))
      (fun x=>«partial» (Dn n) A H0 H1 side true low j (μP (S.law n)) (μA (S.law n)) (x.1:ℝ) (action x))
      (1-(D.regimeShare:ℝ)) (D.regimeShare:ℝ) (hn n false) (hn n true)
  · exact congrArg (fun y : ℝ=>𝓝 y) (FinitePayoffLinearity.test_mix (μz 2) a
      (fun x=>zeroPartial Ds A H0 H1 side false low j (μP S.limit) (μA S.limit) (x.1:ℝ) (action x))
      (fun x=>zeroPartial Ds A H0 H1 side true low j (μP S.limit) (μA S.limit) (x.1:ℝ) (action x))
      (1-(D.regimeShare:ℝ)) (D.regimeShare:ℝ) (hz false) (hz true))

omit [NullSingletonClass ((ProbabilityMeasure.toMeasure (S.limit 0).1).map (fun x=>(x.2:ℝ)))] [NullSingletonClass ((ProbabilityMeasure.toMeasure (S.limit 1).1).map (fun x=>(x.2:ℝ)))] [NullSingletonClass ((ProbabilityMeasure.toMeasure (S.limit 2).1).map (fun x=>(x.2:ℝ)))] in
lemma continuous_noisy_active_mix (k : Fin 3) (A H0 H1 : ℕ) (low : Bool)
    (action : C(Own D P t k,Icc (1:ℝ) D.U)) (n : ℕ) :
    Continuous (fun x=> activeMix (Dn n) A H0 H1 low (μP (S.law n)) (μA (S.law n))
      (x.1:ℝ) (action x)) :=
  (continuous_const.mul (continuous_noisy_active D P t ht N S k A H0 H1 false low action n)).add
    (continuous_const.mul (continuous_noisy_active D P t ht N S k A H0 H1 true low action n))

omit [NullSingletonClass ((ProbabilityMeasure.toMeasure (S.limit 2).1).map (fun x=>(x.2:ℝ)))] in
lemma continuous_zero_active_mix (k : Fin 3) (A H0 H1 : ℕ) (low : Bool)
    (action : C(Own D P t k,Icc (1:ℝ) D.U)) :
    Continuous (fun x=> zeroActiveMix Ds A H0 H1 low (μP S.limit) (μA S.limit)
      (x.1:ℝ) (action x)) :=
  (continuous_const.mul (continuous_zero_active D P t ht N S k A H0 H1 false low action)).add
    (continuous_const.mul (continuous_zero_active D P t ht N S k A H0 H1 true low action))

omit [NullSingletonClass ((ProbabilityMeasure.toMeasure (S.limit 0).1).map (fun x=>(x.2:ℝ)))] [NullSingletonClass ((ProbabilityMeasure.toMeasure (S.limit 1).1).map (fun x=>(x.2:ℝ)))] [NullSingletonClass ((ProbabilityMeasure.toMeasure (S.limit 2).1).map (fun x=>(x.2:ℝ)))] in
lemma continuous_noisy_partial_mix (A H0 H1 : ℕ) (side low : Bool)
    (j : Fin (AllCountAtypical.ownCount H0 H1 side))
    (action : C(Own D P t 2,Icc D.R D.Up)) (n : ℕ) :
    Continuous (fun x=> partialMix (Dn n) A H0 H1 side low j (μP (S.law n)) (μA (S.law n))
      (x.1:ℝ) (action x)) :=
  (continuous_const.mul (continuous_noisy_partial D P t ht N S A H0 H1 side false low j action n)).add
    (continuous_const.mul (continuous_noisy_partial D P t ht N S A H0 H1 side true low j action n))

lemma continuous_zero_partial_mix (A H0 H1 : ℕ) (side low : Bool)
    (j : Fin (AllCountAtypical.ownCount H0 H1 side))
    (action : C(Own D P t 2,Icc D.R D.Up)) :
    Continuous (fun x=> zeroPartialMix Ds A H0 H1 side low j (μP S.limit) (μA S.limit)
      (x.1:ℝ) (action x)) :=
  (continuous_const.mul (continuous_zero_partial D P t ht N S A H0 H1 side false low j action)).add
    (continuous_const.mul (continuous_zero_partial D P t ht N S A H0 H1 side true low j action))

lemma partial_own_mix (A own other : ℕ) (low : Bool) (j : Fin own)
    (action : C(Own D P t 2,Icc D.R D.Up)) (a : C(Own D P t 2,ℝ)) :
    Tendsto (fun n=>∫x,a x*partialOwnMix (Dn n) A own other low j
      (μP (S.law n)) (μA (S.law n)) (x.1:ℝ) (action x) ∂ μn n 2) atTop
      (𝓝 (∫x,a x*zeroPartialOwnMix Ds A own other low j (μP S.limit) (μA S.limit)
        (x.1:ℝ) (action x) ∂ μz 2)) := by
  by_cases h : own ≤ other
  · simpa only [partialOwnMix,zeroPartialOwnMix,if_pos h] using!
      partial_mix D P t ht N S A own other false low j action a
  · simpa only [partialOwnMix,zeroPartialOwnMix,if_neg h] using!
      partial_mix D P t ht N S A other own true low j action a

omit [NullSingletonClass ((ProbabilityMeasure.toMeasure (S.limit 0).1).map (fun x=>(x.2:ℝ)))] [NullSingletonClass ((ProbabilityMeasure.toMeasure (S.limit 1).1).map (fun x=>(x.2:ℝ)))] [NullSingletonClass ((ProbabilityMeasure.toMeasure (S.limit 2).1).map (fun x=>(x.2:ℝ)))] in
lemma continuous_noisy_own_mix (A own other : ℕ) (low : Bool) (j : Fin own)
    (action : C(Own D P t 2,Icc D.R D.Up)) (n : ℕ) :
    Continuous (fun x=>partialOwnMix (Dn n) A own other low j
      (μP (S.law n)) (μA (S.law n)) (x.1:ℝ) (action x)) := by
  by_cases h : own ≤ other
  · simpa only [partialOwnMix,if_pos h] using!
      continuous_noisy_partial_mix D P t ht N S A own other false low j action n
  · simpa only [partialOwnMix,if_neg h] using!
      continuous_noisy_partial_mix D P t ht N S A other own true low j action n

lemma continuous_zero_own_mix (A own other : ℕ) (low : Bool) (j : Fin own)
    (action : C(Own D P t 2,Icc D.R D.Up)) :
    Continuous (fun x=>zeroPartialOwnMix Ds A own other low j
      (μP S.limit) (μA S.limit) (x.1:ℝ) (action x)) := by
  by_cases h : own ≤ other
  · simpa only [zeroPartialOwnMix,if_pos h] using!
      continuous_zero_partial_mix D P t ht N S A own other false low j action
  · simpa only [zeroPartialOwnMix,if_neg h] using!
      continuous_zero_partial_mix D P t ht N S A other own true low j action

attribute [local irreducible] partialOwnMix zeroPartialOwnMix

lemma partial_pattern (kind : Fin N→ Fin 4)
    (action : C(Own D P t 2,Icc D.R D.Up)) (a : C(Own D P t 2,ℝ)) :
    Tendsto (fun n=>∫x,a x*OrderedSourcePayoffExpansion.partialPattern (Dn n) kind
      (μP (S.law n)) (μA (S.law n)) (x.1:ℝ) (action x) ∂ μn n 2) atTop
      (𝓝 (∫x,a x*zeroPartialPattern Ds kind (μP S.limit) (μA S.limit)
        (x.1:ℝ) (action x) ∂ μz 2)) := by
  have h0:=partial_own_mix D P t ht N S ((Ds).count kind 1) ((Ds).count kind 2+1)
    ((Ds).count kind 3) (decide (0< (Ds).count kind 0)) ⟨0,by omega⟩ action a
  have h1:=partial_own_mix D P t ht N S ((Ds).count kind 1) ((Ds).count kind 3+1)
    ((Ds).count kind 2) (decide (0< (Ds).count kind 0)) ⟨0,by omega⟩ action a
  have hn (n : ℕ) (own other : ℕ) (j : Fin own) :=
    FinitePayoffLinearity.continuous_integrable (μn n 2) _
      (a.continuous.mul (continuous_noisy_own_mix D P t ht N S ((Ds).count kind 1) own other
        (decide (0< (Ds).count kind 0)) j action n))
  have hz (own other : ℕ) (j : Fin own) :=
    FinitePayoffLinearity.continuous_integrable (μz 2) _
      (a.continuous.mul (continuous_zero_own_mix D P t ht N S ((Ds).count kind 1) own other
        (decide (0< (Ds).count kind 0)) j action))
  have hh:=(h0.const_mul (1/2:ℝ)).add (h1.const_mul (1/2:ℝ))
  convert! hh using 1
  · funext n
    exact FinitePayoffLinearity.test_mix (μn n 2) a
      (fun x=>partialOwnMix (Dn n) ((Ds).count kind 1) ((Ds).count kind 2+1) ((Ds).count kind 3) (decide (0< (Ds).count kind 0)) ⟨0,by omega⟩
        (μP (S.law n)) (μA (S.law n)) (x.1:ℝ) (action x))
      (fun x=>partialOwnMix (Dn n) ((Ds).count kind 1) ((Ds).count kind 3+1) ((Ds).count kind 2) (decide (0< (Ds).count kind 0)) ⟨0,by omega⟩
        (μP (S.law n)) (μA (S.law n)) (x.1:ℝ) (action x))
      (1/2) (1/2) (hn n _ _ _) (hn n _ _ _)
  · exact congrArg (fun y : ℝ=>𝓝 y) (FinitePayoffLinearity.test_mix (μz 2) a
      (fun x=>zeroPartialOwnMix Ds ((Ds).count kind 1) ((Ds).count kind 2+1) ((Ds).count kind 3) (decide (0< (Ds).count kind 0)) ⟨0,by omega⟩
        (μP S.limit) (μA S.limit) (x.1:ℝ) (action x))
      (fun x=>zeroPartialOwnMix Ds ((Ds).count kind 1) ((Ds).count kind 3+1) ((Ds).count kind 2) (decide (0< (Ds).count kind 0)) ⟨0,by omega⟩
        (μP S.limit) (μA S.limit) (x.1:ℝ) (action x))
      (1/2) (1/2) (hz _ _ _) (hz _ _ _))

omit [NullSingletonClass ((ProbabilityMeasure.toMeasure (S.limit 0).1).map (fun x=>(x.2:ℝ)))] [NullSingletonClass ((ProbabilityMeasure.toMeasure (S.limit 1).1).map (fun x=>(x.2:ℝ)))] [NullSingletonClass ((ProbabilityMeasure.toMeasure (S.limit 2).1).map (fun x=>(x.2:ℝ)))] in
lemma continuous_noisy_pattern (kind : Fin N→ Fin 4)
    (action : C(Own D P t 2,Icc D.R D.Up)) (n : ℕ) :
    Continuous (fun x=>OrderedSourcePayoffExpansion.partialPattern (Dn n) kind
      (μP (S.law n)) (μA (S.law n)) (x.1:ℝ) (action x)) :=
  (continuous_const.mul (continuous_noisy_own_mix D P t ht N S _ _ _ _ _ action n)).add
    (continuous_const.mul (continuous_noisy_own_mix D P t ht N S _ _ _ _ _ action n))

lemma continuous_zero_pattern (kind : Fin N→ Fin 4)
    (action : C(Own D P t 2,Icc D.R D.Up)) :
    Continuous (fun x=>zeroPartialPattern Ds kind (μP S.limit) (μA S.limit)
      (x.1:ℝ) (action x)) :=
  (continuous_const.mul (continuous_zero_own_mix D P t ht N S _ _ _ _ _ action)).add
    (continuous_const.mul (continuous_zero_own_mix D P t ht N S _ _ _ _ _ action))

omit [NullSingletonClass ((ProbabilityMeasure.toMeasure (S.limit 2).1).map (fun x=>(x.2:ℝ)))] in
theorem active_expected (k : Fin 3)
    (action : C(Own D P t k,Icc (1:ℝ) D.U)) (a : C(Own D P t k,ℝ)) :
    Tendsto (fun n=>∫x,a x*OrderedFiniteTailNoisyGame.activeExpected (Dn n) N
      (bidLaws D P t ht (S.law n),((x.1:ℝ),action x)) ∂ μn n k) atTop
      (𝓝 (∫x,a x*OrderedZeroNoiseFiniteGame.activeExpected Ds N
        (bidLaws D P t ht S.limit,((x.1:ℝ),action x)) ∂ μz k)) := by
  have hn (n : ℕ) (kind : Fin N→ Fin 4) := FinitePayoffLinearity.continuous_integrable (μn n k) _
    (a.continuous.mul (continuous_noisy_active_mix D P t ht N S k ((Ds).count kind 1)
      (min ((Ds).count kind 2) ((Ds).count kind 3)) (max ((Ds).count kind 2) ((Ds).count kind 3)) (decide (0< (Ds).count kind 0)) action n))
  have hz (kind : Fin N→ Fin 4) := FinitePayoffLinearity.continuous_integrable (μz k) _
    (a.continuous.mul (continuous_zero_active_mix D P t ht N S k ((Ds).count kind 1)
      (min ((Ds).count kind 2) ((Ds).count kind 3)) (max ((Ds).count kind 2) ((Ds).count kind 3)) (decide (0< (Ds).count kind 0)) action))
  have hen (n : ℕ) := FinitePayoffLinearity.test_sum (μn n k) a
    (fun kind : Fin N→Fin 4=>(CommonList.iid (Ds).categories N).mass kind)
    (fun kind x=>activeMix (Dn n) ((Ds).count kind 1) (min ((Ds).count kind 2) ((Ds).count kind 3)) (max ((Ds).count kind 2) ((Ds).count kind 3)) (decide (0< (Ds).count kind 0)) (μP (S.law n)) (μA (S.law n)) (x.1:ℝ) (action x)) (hn n)
  have hez := FinitePayoffLinearity.test_sum (μz k) a
    (fun kind : Fin N→Fin 4=>(CommonList.iid (Ds).categories N).mass kind)
    (fun kind x=>zeroActiveMix Ds ((Ds).count kind 1) (min ((Ds).count kind 2) ((Ds).count kind 3)) (max ((Ds).count kind 2) ((Ds).count kind 3)) (decide (0< (Ds).count kind 0)) (μP S.limit) (μA S.limit) (x.1:ℝ) (action x)) hz
  have hh : Tendsto (fun n=>∑kind : Fin N→Fin 4,(CommonList.iid (Ds).categories N).mass kind*
      (∫x,a x*activeMix (Dn n) ((Ds).count kind 1) (min ((Ds).count kind 2) ((Ds).count kind 3)) (max ((Ds).count kind 2) ((Ds).count kind 3)) (decide (0< (Ds).count kind 0)) (μP (S.law n)) (μA (S.law n)) (x.1:ℝ) (action x) ∂ μn n k)) atTop
      (𝓝 (∑kind : Fin N→Fin 4,(CommonList.iid (Ds).categories N).mass kind*
        (∫x,a x*zeroActiveMix Ds ((Ds).count kind 1) (min ((Ds).count kind 2) ((Ds).count kind 3)) (max ((Ds).count kind 2) ((Ds).count kind 3)) (decide (0< (Ds).count kind 0)) (μP S.limit) (μA S.limit) (x.1:ℝ) (action x) ∂ μz k))) := by
    apply tendsto_finsetSum
    intro kind _
    exact (active_mix D P t ht N S k ((Ds).count kind 1) (min ((Ds).count kind 2) ((Ds).count kind 3)) (max ((Ds).count kind 2) ((Ds).count kind 3)) (decide (0< (Ds).count kind 0)) action a).const_mul _
  convert! hh using 1
  · funext n
    simpa only [OrderedSourcePayoffExpansion.active_expected] using! hen n
  · exact congrArg (fun y : ℝ=>𝓝 y) (by
      simpa only [OrderedSourcePayoffExpansion.zero_active_expected] using! hez)

theorem partial_expected
    (action : C(Own D P t 2,Icc D.R D.Up)) (a : C(Own D P t 2,ℝ)) :
    Tendsto (fun n=>∫x,a x*OrderedFiniteTailNoisyGame.partialExpected (Dn n) N
      (bidLaws D P t ht (S.law n),((x.1:ℝ),action x)) ∂ μn n 2) atTop
      (𝓝 (∫x,a x*OrderedZeroNoiseFiniteGame.partialExpected Ds N
        (bidLaws D P t ht S.limit,((x.1:ℝ),action x)) ∂ μz 2)) := by
  have hn (n : ℕ) (kind : Fin N→ Fin 4) := FinitePayoffLinearity.continuous_integrable (μn n 2) _
    (a.continuous.mul (continuous_noisy_pattern D P t ht N S kind action n))
  have hz (kind : Fin N→ Fin 4) := FinitePayoffLinearity.continuous_integrable (μz 2) _
    (a.continuous.mul (continuous_zero_pattern D P t ht N S kind action))
  have hen (n : ℕ) := FinitePayoffLinearity.test_sum (μn n 2) a
    (fun kind : Fin N→Fin 4=>(CommonList.iid (Ds).categories N).mass kind)
    (fun kind x=>OrderedSourcePayoffExpansion.partialPattern (Dn n) kind (μP (S.law n)) (μA (S.law n)) (x.1:ℝ) (action x)) (hn n)
  have hez := FinitePayoffLinearity.test_sum (μz 2) a
    (fun kind : Fin N→Fin 4=>(CommonList.iid (Ds).categories N).mass kind)
    (fun kind x=>zeroPartialPattern Ds kind (μP S.limit) (μA S.limit) (x.1:ℝ) (action x)) hz
  have hh : Tendsto (fun n=>∑kind : Fin N→Fin 4,(CommonList.iid (Ds).categories N).mass kind*
      (∫x,a x*OrderedSourcePayoffExpansion.partialPattern (Dn n) kind (μP (S.law n)) (μA (S.law n)) (x.1:ℝ) (action x) ∂ μn n 2)) atTop
      (𝓝 (∑kind : Fin N→Fin 4,(CommonList.iid (Ds).categories N).mass kind*
        (∫x,a x*zeroPartialPattern Ds kind (μP S.limit) (μA S.limit) (x.1:ℝ) (action x) ∂ μz 2))) := by
    apply tendsto_finsetSum
    intro kind _
    exact (partial_pattern D P t ht N S kind action a).const_mul _
  convert! hh using 1
  · funext n
    simpa only [OrderedSourcePayoffExpansion.partial_expected] using! hen n
  · exact congrArg (fun y : ℝ=>𝓝 y) (by
      simpa only [OrderedSourcePayoffExpansion.zero_partial_expected] using! hez)

theorem localized (k : Fin 3)
    (action : C(Own D P t k,ActiveBaseBid (bidLo D k) (bidHi D k)))
    (a : C(Own D P t k,ℝ)) :
    Tendsto (fun n=>∫x,a x*SourceOrderedNoisyFixedPoint.payoff (S.data n) P t ht N k
      (S.law n,(x.1,action x)) ∂ μn n k) atTop
      (𝓝 (∫x,a x*OrderedZeroNoiseFiniteGame.sourcePayoff D P t ht N k
        (S.limit,(x.1,action x)) ∂ μz k)) := by
  fin_cases k
  · let widened : C(Own D P t 0,Icc (1:ℝ) D.U):=
      ⟨fun x=> extendBid D.huU (action x),(continuous_extendBid D.huU).comp action.continuous⟩
    exact active_expected D P t ht N S 0 widened a
  · exact active_expected D P t ht N S 1 action a
  · exact partial_expected D P t ht N S action a

omit [NullSingletonClass ((ProbabilityMeasure.toMeasure (S.limit 2).1).map (fun x=>(x.2:ℝ)))] in
theorem continuous_zero_active_expected (k : Fin 3)
    (action : C(Own D P t k,Icc (1:ℝ) D.U)) :
    Continuous (fun x=> OrderedZeroNoiseFiniteGame.activeExpected Ds N
      (bidLaws D P t ht S.limit,((x.1:ℝ),action x))) := by
  simp_rw [OrderedSourcePayoffExpansion.zero_active_expected]
  apply continuous_finsetSum
  intro kind _
  exact continuous_const.mul
    (continuous_zero_active_mix D P t ht N S k _ _ _ _ action)

theorem continuous_zero_partial_expected
    (action : C(Own D P t 2,Icc D.R D.Up)) :
    Continuous (fun x=> OrderedZeroNoiseFiniteGame.partialExpected Ds N
      (bidLaws D P t ht S.limit,((x.1:ℝ),action x))) := by
  simp_rw [OrderedSourcePayoffExpansion.zero_partial_expected]
  apply continuous_finsetSum
  intro kind _
  exact continuous_const.mul (continuous_zero_pattern D P t ht N S kind action)

theorem continuous_zero (k : Fin 3) :
    Continuous (fun x : Own D P t k=> OrderedZeroNoiseFiniteGame.sourcePayoff D P t ht N k (S.limit,x)) := by
  fin_cases k
  · exact continuous_zero_active_expected D P t ht N S 0
      ⟨fun x=> extendBid D.huU x.2,(continuous_extendBid D.huU).comp continuous_snd⟩
  · exact continuous_zero_active_expected D P t ht N S 1 ⟨Prod.snd,continuous_snd⟩
  · exact continuous_zero_partial_expected D P t ht N S ⟨Prod.snd,continuous_snd⟩

end FCAppendix.Affine.Tail04.OrderedSourcePayoffPassage
