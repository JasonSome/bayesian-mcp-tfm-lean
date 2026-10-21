import FCAppendix.Affine.Tail04.SourceTailNoisyFixedPoint
import FCAppendix.Affine.Tail04.NoisyPrivateLaws
import FCAppendix.Affine.Tail04.EqualPrivateActiveRelabel

noncomputable section
namespace FCAppendix.Affine.Tail04.ZeroNoiseFiniteGame
open MeasureTheory ProbabilityTheory Set Classical
open Existence.Distributional EqualPrivateSignal CompactSourceBidLaws
open FiniteTailNoisyGame SourceTailNoisyFixedPoint
open scoped BigOperators

variable (D : Data)

lemma base_partial_lt_one : D.Up<1 := by
  have hUp : 0≤ D.Up:=D.hR.le.trans D.hRUp
  have hm:=mul_nonneg hUp D.heps.le
  nlinarith [D.hRp]

def sortingRegion : Observable.Regions where
  d:=0
  R:=D.R
  Rp:=D.Up
  U:=1
  H:=2
  d_nonneg:=le_rfl
  d_lt_R:=D.hR
  R_le_Rp:=D.hRUp
  Rp_lt_one:=base_partial_lt_one D
  one_le_U:=le_rfl
  U_lt_H:=by norm_num

def privateEntry (μ : ProbabilityMeasure (Icc D.R D.Up)) :
    ProbabilityMeasure (Unit⊕Icc D.R D.Up) :=
  NoisyPrivateLaws.residualEntryLaw D.upperShare μ

def privateRow (H : ℕ) (μ : ProbabilityMeasure (Icc D.R D.Up)) :
    ProbabilityMeasure (Signal H D.R D.Up) := rowLaw H (privateEntry D μ)

def privateBayes (H : ℕ) (μ : ProbabilityMeasure (Icc D.R D.Up)) :
    WeakProbability.Law (Signal H D.R D.Up) :=
  WeakProbability.mk ((privateRow D H μ).map
    (PrivateRowSorting.continuous_sortSignal (sortingRegion D) H).measurable.aemeasurable)

lemma continuous_privateEntry : Continuous (privateEntry D) :=
  (continuous_mixture D.upperShare).comp (continuous_const.prodMk
    (ProbabilityMeasure.continuous_map continuous_inr))

lemma continuous_privateRow (H : ℕ) : Continuous (privateRow D H) :=
  (continuous_rowLaw H).comp (continuous_privateEntry D)

lemma continuous_privateBayes (H : ℕ) : Continuous (privateBayes D H) :=
  WeakProbability.continuous_mk.comp
    ((ProbabilityMeasure.continuous_map (PrivateRowSorting.continuous_sortSignal (sortingRegion D) H)).comp
      (continuous_privateRow D H))

def activeFiber (A H0 H1 : ℕ) (lowPresent reg : Bool)
    (p : D.ActiveFocal×(Fin A→ Icc (1:ℝ) D.U)) : ℝ :=
  let b:=D.insertActive p.1.2.1 p.2
  if H0=H1 then
    EqualPrivateCountPayoff.utility (A+1) H0 D.c D.R D.Up D.ξ 1 D.U D.eta
      D.heta0 D.heta1 0 (p.1.1,(b,privateBayes D H0 p.1.2.2))
  else
    affineCountUtility
      (UnequalNoisyCountPayoff.rawCount H0 H1 D.c D.ξ D.U D.R D.Up D.width
        (D.e0 reg) D.F reg lowPresent (D.marksLaw H0) (D.marksLaw H1)
        (fun i=>(b i:ℝ)) 0)
      p.1.1 p.1.2.1 D.eta D.heta0 D.heta1

def activeRegimeFiber (A H0 H1 : ℕ) (lowPresent : Bool)
    (p : D.ActiveFocal×(Fin A→ Icc (1:ℝ) D.U)) : ℝ :=
  (1-(D.regimeShare:ℝ))*activeFiber D A H0 H1 lowPresent false p+
    (D.regimeShare:ℝ)*activeFiber D A H0 H1 lowPresent true p

def equalPartialValue (A H : ℕ) (j : Fin H)
    (b : Fin A→ Icc (1:ℝ) D.U) (μ : ProbabilityMeasure (Icc D.R D.Up))
    (price : Icc D.R D.Up) (s : Signal H D.R D.Up) : ℝ :=
  PrivatePayoffContinuity.privateValue (c:=D.c) D.ξ j
    (fun i=>(SortedAllNoise.sortedBox b i:ℝ),
      policyMean A H D.c D.R D.Up D.ξ 1 D.U
        (SortedAllNoise.sortedBox b,privateBayes D H μ),
      Function.update s j (Sum.inr price))

def partialFiber (A H0 H1 : ℕ) (side lowPresent reg : Bool)
    (j : Fin (AllCountAtypical.ownCount H0 H1 side))
    (p : D.PartialFocal×(Fin A→ Icc (1:ℝ) D.U)) : ℝ :=
  (p.1.1-(p.1.2.1:ℝ))*
    if h : H0=H1 then
      let jj : Fin H0:=Fin.cast (by cases side <;> simp [AllCountAtypical.ownCount,h]) j
      ∫ s,equalPartialValue D A H0 jj p.2 p.1.2.2 p.1.2.1 s
        ∂(privateRow D H0 p.1.2.2 : Measure _)
    else
      let w:=UnequalPartialCountPayoff.rawWeight A H0 H1 D.c D.ξ D.U D.R D.Up D.width
        (D.e0 reg) D.F reg lowPresent (D.marksLaw H0) (D.marksLaw H1) (fun i=>(p.2 i:ℝ))
      w*(if reg then 0 else 1)+(1-w)*
        ∫ s,AtypicalPartialNoisy.rankInclusion A H0 H1 D.c side j ((p.1.2.1:ℝ),s)
          ∂(privateRow D (AllCountAtypical.ownCount H0 H1 side) p.1.2.2 : Measure (Signal (AllCountAtypical.ownCount H0 H1 side) D.R D.Up))

def partialRegimeFiber (A H0 H1 : ℕ) (side lowPresent : Bool)
    (j : Fin (AllCountAtypical.ownCount H0 H1 side))
    (p : D.PartialFocal×(Fin A→ Icc (1:ℝ) D.U)) : ℝ :=
  (1-(D.regimeShare:ℝ))*partialFiber D A H0 H1 side lowPresent false j p+
    (D.regimeShare:ℝ)*partialFiber D A H0 H1 side lowPresent true j p

def activeExpected (N : ℕ) (p : D.BidLaws×(ℝ×Icc (1:ℝ) D.U)) : ℝ :=
  ∑ kind : Fin N→ Fin 4,(CommonList.iid D.categories N).mass kind*
    ∫ row : Fin (D.count kind 1)→ Icc (1:ℝ) D.U,
      activeRegimeFiber D (D.count kind 1) (D.count kind 2) (D.count kind 3)
        (decide (0< D.count kind 0)) ((p.2.1,p.2.2,p.1.2.2),row)
        ∂(rowLaw (D.count kind 1) (D.commonLaw p.1) : Measure _)

def partialPattern {N : ℕ} (kind : Fin N→ Fin 4)
    (p : D.PartialFocal×(Fin (D.count kind 1)→ Icc (1:ℝ) D.U)) : ℝ :=
  (1/2:ℝ)*partialRegimeFiber D (D.count kind 1) (D.count kind 2+1) (D.count kind 3)
    false (decide (0< D.count kind 0)) ⟨0,by simp [AllCountAtypical.ownCount]⟩ p+
  (1/2:ℝ)*partialRegimeFiber D (D.count kind 1) (D.count kind 2) (D.count kind 3+1)
    true (decide (0< D.count kind 0)) ⟨0,by simp [AllCountAtypical.ownCount]⟩ p

def partialExpected (N : ℕ) (p : D.BidLaws×(ℝ×Icc D.R D.Up)) : ℝ :=
  ∑ kind : Fin N→ Fin 4,(CommonList.iid D.categories N).mass kind*
    ∫ row : Fin (D.count kind 1)→ Icc (1:ℝ) D.U,
      partialPattern D kind ((p.2.1,p.2.2,p.1.2.2),row)
        ∂(rowLaw (D.count kind 1) (D.commonLaw p.1) : Measure _)

def sourcePayoff (P : ValueParameters) (t : ℝ) (ht : P.M< t) (N : ℕ) :
    ∀ i : Fin 3,JointProfile D P t ht×
      (Hybrid.ActiveValue (valueLo P i) (valueHi P t i)×
        Hybrid.ActiveBaseBid (bidLo D i) (bidHi D i))→ℝ := by
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun i => Fin.elim0 i)))
  · exact fun p=> activeExpected (installOriginal D P t ht) N
      (bidLaws D P t ht p.1,((p.2.1:ℝ),extendBid D.huU p.2.2))
  · exact fun p=> activeExpected (installOriginal D P t ht) N
      (bidLaws D P t ht p.1,((p.2.1:ℝ),p.2.2))
  · exact fun p=> partialExpected (installOriginal D P t ht) N
      (bidLaws D P t ht p.1,((p.2.1:ℝ),p.2.2))

end FCAppendix.Affine.Tail04.ZeroNoiseFiniteGame
