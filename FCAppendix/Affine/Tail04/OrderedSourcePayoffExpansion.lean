import FCAppendix.Affine.Tail04.OrderedSourceFiberIntegrals
import FCAppendix.Affine.Tail04.OrderedZeroNoiseFiniteGame

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedSourcePayoffExpansion
open MeasureTheory ProbabilityTheory Set Classical
open Existence.Distributional EqualPrivateSignal CompactSourceBidLaws
open FiniteTailNoisyGame OrderedSourceFiberIntegrals
open scoped BigOperators

variable (D : Data)

def activeMix (A H0 H1 : ℕ) (low : Bool)
    (μP : ProbabilityMeasure (Icc D.R D.Up)) (μA : ProbabilityMeasure (Icc (1:ℝ) D.U))
    (v : ℝ) (price : Icc (1:ℝ) D.U) : ℝ :=
  (1-(D.regimeShare:ℝ))*active D A H0 H1 false low μP μA v price+
    (D.regimeShare:ℝ)*active D A H0 H1 true low μP μA v price

def zeroActiveMix (A H0 H1 : ℕ) (low : Bool)
    (μP : ProbabilityMeasure (Icc D.R D.Up)) (μA : ProbabilityMeasure (Icc (1:ℝ) D.U))
    (v : ℝ) (price : Icc (1:ℝ) D.U) : ℝ :=
  (1-(D.regimeShare:ℝ))*zeroActive D A H0 H1 false low μP μA v price+
    (D.regimeShare:ℝ)*zeroActive D A H0 H1 true low μP μA v price

def partialMix (A H0 H1 : ℕ) (side low : Bool)
    (j : Fin (AllCountAtypical.ownCount H0 H1 side))
    (μP : ProbabilityMeasure (Icc D.R D.Up)) (μA : ProbabilityMeasure (Icc (1:ℝ) D.U))
    (v : ℝ) (price : Icc D.R D.Up) : ℝ :=
  (1-(D.regimeShare:ℝ))*«partial» D A H0 H1 side false low j μP μA v price+
    (D.regimeShare:ℝ)*«partial» D A H0 H1 side true low j μP μA v price

def zeroPartialMix (A H0 H1 : ℕ) (side low : Bool)
    (j : Fin (AllCountAtypical.ownCount H0 H1 side))
    (μP : ProbabilityMeasure (Icc D.R D.Up)) (μA : ProbabilityMeasure (Icc (1:ℝ) D.U))
    (v : ℝ) (price : Icc D.R D.Up) : ℝ :=
  (1-(D.regimeShare:ℝ))*zeroPartial D A H0 H1 side false low j μP μA v price+
    (D.regimeShare:ℝ)*zeroPartial D A H0 H1 side true low j μP μA v price

lemma active_regime (A H0 H1 : ℕ) (low : Bool)
    (μP : ProbabilityMeasure (Icc D.R D.Up)) (μA : ProbabilityMeasure (Icc (1:ℝ) D.U))
    (v : ℝ) (price : Icc (1:ℝ) D.U) :
    (∫b,D.activeRegimeFiber A H0 H1 low ((v,price,μP),b) ∂(rowLaw A μA : Measure _))=
      activeMix D A H0 H1 low μP μA v price :=
  FinitePayoffLinearity.row_mix _ _ _ _ _
    (active_row_integrable D A H0 H1 false low μP μA v price)
    (active_row_integrable D A H0 H1 true low μP μA v price)

lemma zero_active_regime (A H0 H1 : ℕ) (low : Bool)
    (μP : ProbabilityMeasure (Icc D.R D.Up)) (μA : ProbabilityMeasure (Icc (1:ℝ) D.U))
    (v : ℝ) (price : Icc (1:ℝ) D.U) :
    (∫b,ZeroNoiseFiniteGame.activeRegimeFiber D A H0 H1 low ((v,price,μP),b)
      ∂(rowLaw A μA : Measure _))=zeroActiveMix D A H0 H1 low μP μA v price :=
  FinitePayoffLinearity.row_mix _ _ _ _ _
    (ZeroFiberBounds.active_integrable D A H0 H1 false low μP v price μA)
    (ZeroFiberBounds.active_integrable D A H0 H1 true low μP v price μA)

lemma partial_regime (A H0 H1 : ℕ) (side low : Bool)
    (j : Fin (AllCountAtypical.ownCount H0 H1 side))
    (μP : ProbabilityMeasure (Icc D.R D.Up)) (μA : ProbabilityMeasure (Icc (1:ℝ) D.U))
    (v : ℝ) (price : Icc D.R D.Up) :
    (∫b,D.partialRegimeFiber A H0 H1 side low j ((v,price,μP),b)
      ∂(rowLaw A μA : Measure _))=partialMix D A H0 H1 side low j μP μA v price :=
  FinitePayoffLinearity.row_mix _ _ _ _ _
    (partial_row_integrable D A H0 H1 side false low j μP μA v price)
    (partial_row_integrable D A H0 H1 side true low j μP μA v price)

lemma zero_partial_regime (A H0 H1 : ℕ) (side low : Bool)
    (j : Fin (AllCountAtypical.ownCount H0 H1 side))
    (μP : ProbabilityMeasure (Icc D.R D.Up)) (μA : ProbabilityMeasure (Icc (1:ℝ) D.U))
    (v : ℝ) (price : Icc D.R D.Up) :
    (∫b,ZeroNoiseFiniteGame.partialRegimeFiber D A H0 H1 side low j ((v,price,μP),b)
      ∂(rowLaw A μA : Measure _))=zeroPartialMix D A H0 H1 side low j μP μA v price :=
  FinitePayoffLinearity.row_mix _ _ _ _ _
    (ZeroFiberBounds.partial_integrable D A H0 H1 false low μP v side j price μA)
    (ZeroFiberBounds.partial_integrable D A H0 H1 true low μP v side j price μA)

def partialOwnMix (A own other : ℕ) (low : Bool) (j : Fin own)
    (μP : ProbabilityMeasure (Icc D.R D.Up)) (μA : ProbabilityMeasure (Icc (1:ℝ) D.U))
    (v : ℝ) (price : Icc D.R D.Up) : ℝ :=
  if own ≤ other then partialMix D A own other false low j μP μA v price
  else partialMix D A other own true low j μP μA v price

def zeroPartialOwnMix (A own other : ℕ) (low : Bool) (j : Fin own)
    (μP : ProbabilityMeasure (Icc D.R D.Up)) (μA : ProbabilityMeasure (Icc (1:ℝ) D.U))
    (v : ℝ) (price : Icc D.R D.Up) : ℝ :=
  if own ≤ other then zeroPartialMix D A own other false low j μP μA v price
  else zeroPartialMix D A other own true low j μP μA v price

lemma partial_own_regime (A own other : ℕ) (low : Bool) (j : Fin own)
    (μP : ProbabilityMeasure (Icc D.R D.Up)) (μA : ProbabilityMeasure (Icc (1:ℝ) D.U))
    (v : ℝ) (price : Icc D.R D.Up) :
    (∫ b,OrderedFiniteTailNoisyGame.partialOwnRegimeFiber D A own other low j
      ((v,price,μP),b) ∂(rowLaw A μA : Measure _)) =
        partialOwnMix D A own other low j μP μA v price := by
  by_cases h : own ≤ other
  · simp only [OrderedFiniteTailNoisyGame.partialOwnRegimeFiber,partialOwnMix,if_pos h]
    exact partial_regime D A own other false low j μP μA v price
  · simp only [OrderedFiniteTailNoisyGame.partialOwnRegimeFiber,partialOwnMix,if_neg h]
    exact partial_regime D A other own true low j μP μA v price

lemma zero_partial_own_regime (A own other : ℕ) (low : Bool) (j : Fin own)
    (μP : ProbabilityMeasure (Icc D.R D.Up)) (μA : ProbabilityMeasure (Icc (1:ℝ) D.U))
    (v : ℝ) (price : Icc D.R D.Up) :
    (∫ b,OrderedZeroNoiseFiniteGame.partialOwnRegimeFiber D A own other low j
      ((v,price,μP),b) ∂(rowLaw A μA : Measure _)) =
        zeroPartialOwnMix D A own other low j μP μA v price := by
  by_cases h : own ≤ other
  · simp only [OrderedZeroNoiseFiniteGame.partialOwnRegimeFiber,zeroPartialOwnMix,if_pos h]
    exact zero_partial_regime D A own other false low j μP μA v price
  · simp only [OrderedZeroNoiseFiniteGame.partialOwnRegimeFiber,zeroPartialOwnMix,if_neg h]
    exact zero_partial_regime D A other own true low j μP μA v price

lemma partial_own_integrable (A own other : ℕ) (low : Bool) (j : Fin own)
    (μP : ProbabilityMeasure (Icc D.R D.Up)) (μA : ProbabilityMeasure (Icc (1:ℝ) D.U))
    (v : ℝ) (price : Icc D.R D.Up) :
    Integrable (fun b=>OrderedFiniteTailNoisyGame.partialOwnRegimeFiber D A own other low j
      ((v,price,μP),b)) (rowLaw A μA : Measure _) :=
  FinitePayoffLinearity.continuous_integrable _ _
    ((OrderedFiniteTailNoisyGame.continuous_partialOwnRegimeFiber D A own other low j).comp
      (continuous_const.prodMk continuous_id))

lemma zero_partial_own_integrable (A own other : ℕ) (low : Bool) (j : Fin own)
    (μP : ProbabilityMeasure (Icc D.R D.Up)) (μA : ProbabilityMeasure (Icc (1:ℝ) D.U))
    (v : ℝ) (price : Icc D.R D.Up) :
    Integrable (fun b=>OrderedZeroNoiseFiniteGame.partialOwnRegimeFiber D A own other low j
      ((v,price,μP),b)) (rowLaw A μA : Measure _) := by
  have hi (H0 H1 : ℕ) (side : Bool) (j : Fin (AllCountAtypical.ownCount H0 H1 side)) :
      Integrable (fun b=>ZeroNoiseFiniteGame.partialRegimeFiber D A H0 H1 side low j
        ((v,price,μP),b)) (rowLaw A μA : Measure _) :=
    ((ZeroFiberBounds.partial_integrable D A H0 H1 false low μP v side j price μA).const_mul
      (1-(D.regimeShare:ℝ))).add
      ((ZeroFiberBounds.partial_integrable D A H0 H1 true low μP v side j price μA).const_mul
        (D.regimeShare:ℝ))
  by_cases h : own ≤ other
  · simp only [OrderedZeroNoiseFiniteGame.partialOwnRegimeFiber,if_pos h]
    exact hi own other false j
  · simp only [OrderedZeroNoiseFiniteGame.partialOwnRegimeFiber,if_neg h]
    exact hi other own true j

def partialPattern {N : ℕ} (kind : Fin N→ Fin 4)
    (μP : ProbabilityMeasure (Icc D.R D.Up)) (μA : ProbabilityMeasure (Icc (1:ℝ) D.U))
    (v : ℝ) (price : Icc D.R D.Up) : ℝ :=
  (1/2:ℝ)*partialOwnMix D (D.count kind 1) (D.count kind 2+1) (D.count kind 3)
    (decide (0< D.count kind 0)) ⟨0,by omega⟩ μP μA v price+
  (1/2:ℝ)*partialOwnMix D (D.count kind 1) (D.count kind 3+1) (D.count kind 2)
    (decide (0< D.count kind 0)) ⟨0,by omega⟩ μP μA v price

def zeroPartialPattern {N : ℕ} (kind : Fin N→ Fin 4)
    (μP : ProbabilityMeasure (Icc D.R D.Up)) (μA : ProbabilityMeasure (Icc (1:ℝ) D.U))
    (v : ℝ) (price : Icc D.R D.Up) : ℝ :=
  (1/2:ℝ)*zeroPartialOwnMix D (D.count kind 1) (D.count kind 2+1) (D.count kind 3)
    (decide (0< D.count kind 0)) ⟨0,by omega⟩ μP μA v price+
  (1/2:ℝ)*zeroPartialOwnMix D (D.count kind 1) (D.count kind 3+1) (D.count kind 2)
    (decide (0< D.count kind 0)) ⟨0,by omega⟩ μP μA v price

lemma partial_pattern {N : ℕ} (kind : Fin N→ Fin 4)
    (μP : ProbabilityMeasure (Icc D.R D.Up)) (μA : ProbabilityMeasure (Icc (1:ℝ) D.U))
    (v : ℝ) (price : Icc D.R D.Up) :
    (∫ b,OrderedFiniteTailNoisyGame.partialPattern D kind ((v,price,μP),b)
      ∂(rowLaw (D.count kind 1) μA : Measure _))=partialPattern D kind μP μA v price := by
  unfold OrderedFiniteTailNoisyGame.partialPattern partialPattern
  rw [FinitePayoffLinearity.row_mix _ _ _ _ _
    (partial_own_integrable D _ _ _ _ _ μP μA v price)
    (partial_own_integrable D _ _ _ _ _ μP μA v price),partial_own_regime,partial_own_regime]

lemma zero_partial_pattern {N : ℕ} (kind : Fin N→ Fin 4)
    (μP : ProbabilityMeasure (Icc D.R D.Up)) (μA : ProbabilityMeasure (Icc (1:ℝ) D.U))
    (v : ℝ) (price : Icc D.R D.Up) :
    (∫ b,OrderedZeroNoiseFiniteGame.partialPattern D kind ((v,price,μP),b)
      ∂(rowLaw (D.count kind 1) μA : Measure _))=zeroPartialPattern D kind μP μA v price := by
  unfold OrderedZeroNoiseFiniteGame.partialPattern zeroPartialPattern
  rw [FinitePayoffLinearity.row_mix _ _ _ _ _
    (zero_partial_own_integrable D _ _ _ _ _ μP μA v price)
    (zero_partial_own_integrable D _ _ _ _ _ μP μA v price),zero_partial_own_regime,zero_partial_own_regime]

lemma active_expected (N : ℕ) (p : D.BidLaws) (v : ℝ) (price : Icc (1:ℝ) D.U) :
    OrderedFiniteTailNoisyGame.activeExpected D N (p,(v,price))=
      ∑kind : Fin N→ Fin 4,(CommonList.iid D.categories N).mass kind*
        activeMix D (D.count kind 1) (min (D.count kind 2) (D.count kind 3))
          (max (D.count kind 2) (D.count kind 3))
          (decide (0< D.count kind 0)) p.2.2 (D.commonLaw p) v price := by
  simp only [OrderedFiniteTailNoisyGame.activeExpected,
    OrderedFiniteTailNoisyGame.activeRegimeFiber,active_regime]

lemma zero_active_expected (N : ℕ) (p : D.BidLaws) (v : ℝ) (price : Icc (1:ℝ) D.U) :
    OrderedZeroNoiseFiniteGame.activeExpected D N (p,(v,price))=
      ∑kind : Fin N→ Fin 4,(CommonList.iid D.categories N).mass kind*
        zeroActiveMix D (D.count kind 1) (min (D.count kind 2) (D.count kind 3))
          (max (D.count kind 2) (D.count kind 3))
          (decide (0< D.count kind 0)) p.2.2 (D.commonLaw p) v price := by
  simp only [OrderedZeroNoiseFiniteGame.activeExpected,
    OrderedZeroNoiseFiniteGame.activeRegimeFiber,zero_active_regime]

lemma partial_expected (N : ℕ) (p : D.BidLaws) (v : ℝ) (price : Icc D.R D.Up) :
    OrderedFiniteTailNoisyGame.partialExpected D N (p,(v,price))=
      ∑kind : Fin N→ Fin 4,(CommonList.iid D.categories N).mass kind*
        partialPattern D kind p.2.2 (D.commonLaw p) v price := by
  simp only [OrderedFiniteTailNoisyGame.partialExpected,partial_pattern]

lemma zero_partial_expected (N : ℕ) (p : D.BidLaws) (v : ℝ) (price : Icc D.R D.Up) :
    OrderedZeroNoiseFiniteGame.partialExpected D N (p,(v,price))=
      ∑kind : Fin N→ Fin 4,(CommonList.iid D.categories N).mass kind*
        zeroPartialPattern D kind p.2.2 (D.commonLaw p) v price := by
  simp only [OrderedZeroNoiseFiniteGame.partialExpected,zero_partial_pattern]

end FCAppendix.Affine.Tail04.OrderedSourcePayoffExpansion
