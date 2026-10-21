import FCAppendix.Affine.Tail04.EqualNoisyUtilities
import FCAppendix.Affine.Tail04.UnequalPartialCountPayoff

noncomputable section
namespace FCAppendix.Affine.Tail04.FiniteTailNoisyGame
open MeasureTheory ProbabilityTheory Set Classical
open Existence.Distributional EqualPrivateSignal CompactSourceBidLaws
open scoped BigOperators

structure Data where
  c : ℕ
  R : ℝ
  Up : ℝ
  U : ℝ
  u : ℝ
  F : ℝ
  ξ : ℝ
  eps : ℝ
  eta : ℝ
  eA : ℝ
  eR : ℝ
  width : ℝ
  hR : 0< R
  hRUp : R≤ Up
  hU : 1≤ U
  hu : 0≤ u
  huU : 1+u≤ U
  heps : 0< eps
  hRp : Up*(1+eps)<1
  hξ : 0< ξ
  hξ1 : ξ<1
  hgap : (1-ξ)*(U*(1+eps))< R
  hF : 1< F
  hUF : U*(1+eps)≤ F
  heA0 : 0≤ eA
  heA1 : eA≤1
  heR0 : 0≤ eR
  heR1 : eR≤1
  hw : 0< width
  heta0 : 0≤ eta
  heta1 : eta≤1
  regimeShare : unitInterval
  bulkShare : unitInterval
  upperShare : unitInterval
  categories : FiniteLaw (Fin 4)

namespace Data
variable (D : Data)

def e0 (reg : Bool) : ℝ := if reg then D.eR else D.eA
def B : ℝ := D.U*(1+D.eps)
def V : ℝ := D.Up*(1+D.eps)

def sortingRegion : Observable.Regions where
  d:=0
  R:=D.R
  Rp:=D.V
  U:=1
  H:=2
  d_nonneg:=le_rfl
  d_lt_R:=D.hR
  R_le_Rp:=by
    have hUp : 0≤ D.Up := D.hR.le.trans D.hRUp
    dsimp [V]
    nlinarith [D.hRUp,mul_nonneg hUp D.heps.le]
  Rp_lt_one:=D.hRp
  one_le_U:=le_rfl
  U_lt_H:=by norm_num

def marksLaw (H : ℕ) : FiniteLaw (Marks H) :=
  SortedPrivateMarks.law H D.upperShare D.upperShare.2.1 D.upperShare.2.2

def privateBayes (H : ℕ) (μ : ProbabilityMeasure (Icc D.R D.Up)) :
    ProbabilityMeasure (Signal H D.R D.V) :=
  privateBayesLaw D.sortingRegion D.hR D.heps.le rfl D.upperShare H μ

lemma continuous_privateBayes (H : ℕ) : Continuous (D.privateBayes H) :=
  continuous_privateBayesLaw D.sortingRegion D.hR D.heps.le rfl D.upperShare H

def privateFocalRow (H : ℕ) (μ : ProbabilityMeasure (Icc D.R D.Up)) :
    ProbabilityMeasure (Signal H D.R D.V) := rawPrivateRow D.hR D.heps.le D.upperShare H μ

lemma continuous_privateFocalRow (H : ℕ) : Continuous (D.privateFocalRow H) :=
  continuous_rawPrivateRow D.hR D.heps.le D.upperShare H

abbrev BidLaws := ProbabilityMeasure (Icc (1:ℝ) (1+D.u))×
  ProbabilityMeasure (Icc (1:ℝ) D.U)×ProbabilityMeasure (Icc D.R D.Up)

def commonLaw (p : D.BidLaws) : ProbabilityMeasure (Icc (1:ℝ) D.U) :=
  activeBaseLaw D.huU D.bulkShare p.1 p.2.1

lemma continuous_commonLaw : Continuous D.commonLaw :=
  (continuous_activeBaseLaw D.huU D.bulkShare).comp
    (continuous_fst.prodMk (continuous_fst.comp continuous_snd))

abbrev ActiveFocal := ℝ×Icc (1:ℝ) D.U×ProbabilityMeasure (Icc D.R D.Up)
abbrev PartialFocal := ℝ×Icc D.R D.Up×ProbabilityMeasure (Icc D.R D.Up)

def insertActive {A : ℕ} (b : Icc (1:ℝ) D.U) (row : Fin A → Icc (1:ℝ) D.U) :
    Fin (A+1) → Icc (1:ℝ) D.U := Fin.cons b row

lemma continuous_insertActive (A : ℕ) :
    Continuous (fun p : Icc (1:ℝ) D.U×(Fin A → Icc (1:ℝ) D.U) => D.insertActive p.1 p.2) := by
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact continuous_fst
  · exact (continuous_apply j).comp continuous_snd

def activeFiber (A H0 H1 : ℕ) (lowPresent reg : Bool)
    (p : D.ActiveFocal×(Fin A → Icc (1:ℝ) D.U)) : ℝ :=
  let b := D.insertActive p.1.2.1 p.2
  if H0=H1 then
    EqualNoisyUtilities.activeUtility (c:=D.c) D.heps.le D.ξ D.eta D.heta0 D.heta1 0
      (p.1.1,(b,D.privateBayes H0 p.1.2.2))
  else
    UnequalNoisyCountPayoff.utility H0 H1 D.c D.ξ D.B D.R D.V D.width (D.e0 reg) D.F D.eps D.eta
      reg lowPresent D.heta0 D.heta1 (D.marksLaw H0) (D.marksLaw H1) 0
      (p.1.1,fun i => (b i:ℝ))

theorem continuous_activeFiber (A H0 H1 : ℕ) (lowPresent reg : Bool) :
    Continuous (D.activeFiber A H0 H1 lowPresent reg) := by
  have hb : Continuous (fun p : D.ActiveFocal×(Fin A → Icc (1:ℝ) D.U) =>
      D.insertActive p.1.2.1 p.2) :=
    (D.continuous_insertActive A).comp
      ((continuous_fst.comp (continuous_snd.comp continuous_fst)).prodMk continuous_snd)
  have hv : Continuous (fun p : D.ActiveFocal×(Fin A → Icc (1:ℝ) D.U) => p.1.1) :=
    continuous_fst.comp continuous_fst
  have hP : Continuous (fun p : D.ActiveFocal×(Fin A → Icc (1:ℝ) D.U) =>
      D.privateBayes H0 p.1.2.2) :=
    (D.continuous_privateBayes H0).comp (continuous_snd.comp (continuous_snd.comp continuous_fst))
  unfold activeFiber
  split_ifs
  · exact (EqualNoisyUtilities.continuous_activeUtility D.heps D.hξ D.eta D.heta0 D.heta1 0).comp
      (hv.prodMk (hb.prodMk hP))
  · apply continuous_iff_continuousAt.mpr
    intro p
    have hreal : Continuous (fun p : D.ActiveFocal×(Fin A → Icc (1:ℝ) D.U) =>
        fun i => (D.insertActive p.1.2.1 p.2 i:ℝ)) :=
      continuous_pi (fun i => continuous_subtype_val.comp ((continuous_apply i).comp hb))
    exact (UnequalNoisyCountPayoff.continuousAt_utility H0 H1 D.c D.ξ D.B D.R D.V
      D.width (D.e0 reg) D.F D.eta reg lowPresent D.heps D.heta0 D.heta1
      (D.marksLaw H0) (D.marksLaw H1) 0 _
      (fun i => lt_of_lt_of_le (by norm_num) (D.insertActive p.1.2.1 p.2 i).2.1)).comp
        (hv.prodMk hreal).continuousAt

def activeRegimeFiber (A H0 H1 : ℕ) (lowPresent : Bool)
    (p : D.ActiveFocal×(Fin A → Icc (1:ℝ) D.U)) : ℝ :=
  (1-(D.regimeShare:ℝ))*D.activeFiber A H0 H1 lowPresent false p+
    (D.regimeShare:ℝ)*D.activeFiber A H0 H1 lowPresent true p

theorem continuous_activeRegimeFiber (A H0 H1 : ℕ) (lowPresent : Bool) :
    Continuous (D.activeRegimeFiber A H0 H1 lowPresent) :=
  (continuous_const.mul (D.continuous_activeFiber A H0 H1 lowPresent false)).add
    (continuous_const.mul (D.continuous_activeFiber A H0 H1 lowPresent true))

def partialFiber (A H0 H1 : ℕ) (side lowPresent reg : Bool)
    (j : Fin (AllCountAtypical.ownCount H0 H1 side))
    (p : D.PartialFocal×(Fin A → Icc (1:ℝ) D.U)) : ℝ :=
  if h : H0=H1 then
    let jj : Fin H0 := Fin.cast (by cases side <;> simp [AllCountAtypical.ownCount,h]) j
    EqualNoisyUtilities.privateUtility (c:=D.c) D.hR D.heps.le D.ξ jj
      (p.1.1,((p.2,D.privateBayes H0 p.1.2.2),p.1.2.1,D.privateFocalRow H0 p.1.2.2))
  else
    UnequalPartialCountPayoff.utility A H0 H1 D.c D.ξ D.B D.R D.Up D.width (D.e0 reg) D.F D.eps
      side reg lowPresent (D.marksLaw H0) (D.marksLaw H1) j
      (p.1.1,(fun i => (p.2 i:ℝ)),p.1.2.1,
        D.privateFocalRow (AllCountAtypical.ownCount H0 H1 side) p.1.2.2)

theorem continuous_partialFiber (A H0 H1 : ℕ) (side lowPresent reg : Bool)
    (j : Fin (AllCountAtypical.ownCount H0 H1 side)) :
    Continuous (D.partialFiber A H0 H1 side lowPresent reg j) := by
  have hv : Continuous (fun p : D.PartialFocal×(Fin A → Icc (1:ℝ) D.U) => p.1.1) :=
    continuous_fst.comp continuous_fst
  have hbid : Continuous (fun p : D.PartialFocal×(Fin A → Icc (1:ℝ) D.U) => p.1.2.1) :=
    continuous_fst.comp (continuous_snd.comp continuous_fst)
  have hμ : Continuous (fun p : D.PartialFocal×(Fin A → Icc (1:ℝ) D.U) => p.1.2.2) :=
    continuous_snd.comp (continuous_snd.comp continuous_fst)
  unfold partialFiber
  split_ifs with h
  · exact (EqualNoisyUtilities.continuous_privateUtility D.hR D.heps D.hξ _).comp
      (hv.prodMk ((continuous_snd.prodMk ((D.continuous_privateBayes H0).comp hμ)).prodMk
        (hbid.prodMk ((D.continuous_privateFocalRow H0).comp hμ))))
  · apply continuous_iff_continuousAt.mpr
    intro p
    have hb : Continuous (fun p : D.PartialFocal×(Fin A → Icc (1:ℝ) D.U) => fun i => (p.2 i:ℝ)) :=
      continuous_pi (fun i => continuous_subtype_val.comp ((continuous_apply i).comp continuous_snd))
    exact (UnequalPartialCountPayoff.continuousAt_utility A H0 H1 D.c D.ξ D.B D.R D.Up
      D.width (D.e0 reg) D.F side reg lowPresent D.heps D.hR (D.marksLaw H0) (D.marksLaw H1) j _
      (fun i => lt_of_lt_of_le (by norm_num) (p.2 i).2.1)).comp
        (hv.prodMk (hb.prodMk (hbid.prodMk
          ((D.continuous_privateFocalRow _).comp hμ)))).continuousAt

def partialRegimeFiber (A H0 H1 : ℕ) (side lowPresent : Bool)
    (j : Fin (AllCountAtypical.ownCount H0 H1 side))
    (p : D.PartialFocal×(Fin A → Icc (1:ℝ) D.U)) : ℝ :=
  (1-(D.regimeShare:ℝ))*D.partialFiber A H0 H1 side lowPresent false j p+
    (D.regimeShare:ℝ)*D.partialFiber A H0 H1 side lowPresent true j p

theorem continuous_partialRegimeFiber (A H0 H1 : ℕ) (side lowPresent : Bool)
    (j : Fin (AllCountAtypical.ownCount H0 H1 side)) :
    Continuous (D.partialRegimeFiber A H0 H1 side lowPresent j) :=
  (continuous_const.mul (D.continuous_partialFiber A H0 H1 side lowPresent false j)).add
    (continuous_const.mul (D.continuous_partialFiber A H0 H1 side lowPresent true j))

def count (_D : Data) {N : ℕ} (kind : Fin N → Fin 4) (k : Fin 4) : ℕ :=
  (Finset.univ.filter (fun i => kind i=k)).card

def activeExpected (N : ℕ) (p : D.BidLaws×(ℝ×Icc (1:ℝ) D.U)) : ℝ :=
  ∑ kind : Fin N → Fin 4,(CommonList.iid D.categories N).mass kind*
    ∫ row : Fin (D.count kind 1) → Icc (1:ℝ) D.U,
      D.activeRegimeFiber (D.count kind 1) (D.count kind 2) (D.count kind 3)
        (decide (0< D.count kind 0)) ((p.2.1,p.2.2,p.1.2.2),row)
        ∂(rowLaw (D.count kind 1) (D.commonLaw p.1) : Measure _)

theorem continuous_activeExpected (N : ℕ) : Continuous (D.activeExpected N) := by
  unfold activeExpected
  apply continuous_finsetSum
  intro kind _
  apply continuous_const.mul
  have hi := continuous_law_integral
    (D.activeRegimeFiber (D.count kind 1) (D.count kind 2) (D.count kind 3)
      (decide (0< D.count kind 0)))
    (D.continuous_activeRegimeFiber _ _ _ _)
  have hf : Continuous (fun p : D.BidLaws×(ℝ×Icc (1:ℝ) D.U) =>
      (p.2.1,p.2.2,p.1.2.2)) := by fun_prop
  exact hi.comp (hf.prodMk
    ((continuous_rowLaw _).comp (D.continuous_commonLaw.comp continuous_fst)))

def partialPattern {N : ℕ} (kind : Fin N → Fin 4)
    (p : D.PartialFocal×(Fin (D.count kind 1) → Icc (1:ℝ) D.U)) : ℝ :=
  (1/2:ℝ)*D.partialRegimeFiber (D.count kind 1) (D.count kind 2+1) (D.count kind 3)
    false (decide (0< D.count kind 0)) ⟨0,by simp [AllCountAtypical.ownCount]⟩ p+
  (1/2:ℝ)*D.partialRegimeFiber (D.count kind 1) (D.count kind 2) (D.count kind 3+1)
    true (decide (0< D.count kind 0)) ⟨0,by simp [AllCountAtypical.ownCount]⟩ p

theorem continuous_partialPattern {N : ℕ} (kind : Fin N → Fin 4) :
    Continuous (D.partialPattern kind) :=
  (continuous_const.mul (D.continuous_partialRegimeFiber _ _ _ false _ _)).add
    (continuous_const.mul (D.continuous_partialRegimeFiber _ _ _ true _ _))

def partialExpected (N : ℕ) (p : D.BidLaws×(ℝ×Icc D.R D.Up)) : ℝ :=
  ∑ kind : Fin N → Fin 4,(CommonList.iid D.categories N).mass kind*
    ∫ row : Fin (D.count kind 1) → Icc (1:ℝ) D.U,
      D.partialPattern kind ((p.2.1,p.2.2,p.1.2.2),row)
        ∂(rowLaw (D.count kind 1) (D.commonLaw p.1) : Measure _)

theorem continuous_partialExpected (N : ℕ) : Continuous (D.partialExpected N) := by
  unfold partialExpected
  apply continuous_finsetSum
  intro kind _
  apply continuous_const.mul
  have hi := continuous_law_integral (D.partialPattern kind) (D.continuous_partialPattern kind)
  have hf : Continuous (fun p : D.BidLaws×(ℝ×Icc D.R D.Up) =>
      (p.2.1,p.2.2,p.1.2.2)) := by fun_prop
  exact hi.comp (hf.prodMk
    ((continuous_rowLaw _).comp (D.continuous_commonLaw.comp continuous_fst)))

end Data
end FCAppendix.Affine.Tail04.FiniteTailNoisyGame
