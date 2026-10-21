import FCAppendix.Affine.Tail04.SourceBoxCoherence
import FCAppendix.Affine.Tail04.BoundedProbabilityIntegral

noncomputable section
namespace FCAppendix.Affine.Tail04.AmbientFiniteGame
open MeasureTheory ProbabilityTheory Set Classical
open Existence.Distributional EqualPrivateSignal CompactSourceBidLaws FixedAmbientNoise
open FiniteTailNoisyGame SourceAmbientLaws
open scoped BigOperators

variable (D : Data)

def activeCount (A H0 H1 : ℕ) (reg low : Bool) (e : Noise D.eps)
    (μP : ProbabilityMeasure (Icc D.R D.Up)) (_v : ℝ) (price : Icc (1:ℝ) D.U)
    (b : Fin A→ Icc (1:ℝ) D.B) (u : unitInterval) : CountLaw 2 :=
  let row:=Fin.cons (physical (by norm_num) D.hU (e,price,u)) b
  if H0=H1 then
    EqualPrivateCountPayoff.countLaw (A+1) H0 D.c D.R D.V D.ξ 1 D.B
      (row,SourceAmbientLaws.privateBayes D H0 e μP) 0
  else
    UnequalNoisyCountPayoff.rawCount H0 H1 D.c D.ξ (D.U*(1+(e:ℝ))) D.R
      (D.Up*(1+(e:ℝ))) D.width (D.e0 reg) D.F reg low
      (D.marksLaw H0) (D.marksLaw H1) (fun i=>(row i:ℝ)) 0

def activeValue (A H0 H1 : ℕ) (reg low : Bool) (e : Noise D.eps)
    (μP : ProbabilityMeasure (Icc D.R D.Up)) (v : ℝ) (price : Icc (1:ℝ) D.U)
    (b : Fin A→ Icc (1:ℝ) D.B) (u : unitInterval) : ℝ :=
  affineCountUtility (activeCount D A H0 H1 reg low e μP v price b u) v
    (physical (by norm_num) D.hU (e,price,u)) D.eta D.heta0 D.heta1

def active (A H0 H1 : ℕ) (reg low : Bool) (e : Noise D.eps)
    (μP : ProbabilityMeasure (Icc D.R D.Up)) (μA : ProbabilityMeasure (Icc (1:ℝ) D.U))
    (v : ℝ) (price : Icc (1:ℝ) D.U) : ℝ :=
  ∫b,∫u : unitInterval,activeValue D A H0 H1 reg low e μP v price b u
    ∂(volume : Measure unitInterval) ∂(rowLaw A (SourceAmbientLaws.common D e μA) : Measure _)

def equalPrivateValue (A H : ℕ) (j : Fin H) (e : Noise D.eps)
    (μP : ProbabilityMeasure (Icc D.R D.Up)) (v : ℝ) (price : Icc D.R D.Up)
    (b : Fin A→ Icc (1:ℝ) D.B) (s : Signal H D.R D.V) (u : unitInterval) : ℝ :=
  (v-(physical D.hR D.hRUp (e,price,u):ℝ))*
    PrivatePayoffContinuity.privateValue (c:=D.c) D.ξ j
      (fun i=>(SortedAllNoise.sortedBox b i:ℝ),
        policyMean A H D.c D.R D.V D.ξ 1 D.B
          (SortedAllNoise.sortedBox b,SourceAmbientLaws.privateBayes D H e μP),
        Function.update s j (Sum.inr (physical D.hR D.hRUp (e,price,u))))

def unequalPrivateValue (A H0 H1 : ℕ) (side reg low : Bool)
    (j : Fin (AllCountAtypical.ownCount H0 H1 side)) (e : Noise D.eps)
    (v : ℝ) (price : Icc D.R D.Up) (b : Fin A→ Icc (1:ℝ) D.B)
    (s : Signal (AllCountAtypical.ownCount H0 H1 side) D.R D.V) (u : unitInterval) : ℝ :=
  let p:=(physical D.hR D.hRUp (e,price,u):ℝ)
  let w:=UnequalPartialCountPayoff.rawWeight A H0 H1 D.c D.ξ (D.U*(1+(e:ℝ))) D.R
    (D.Up*(1+(e:ℝ))) D.width (D.e0 reg) D.F reg low
    (D.marksLaw H0) (D.marksLaw H1) (fun i=>(b i:ℝ))
  (v-p)*(w*(if reg then 0 else 1)+(1-w)*
    AtypicalPartialNoisy.rankInclusion A H0 H1 D.c side j (p,s))

def «partial» (A H0 H1 : ℕ) (side reg low : Bool)
    (j : Fin (AllCountAtypical.ownCount H0 H1 side)) (e : Noise D.eps)
    (μP : ProbabilityMeasure (Icc D.R D.Up)) (μA : ProbabilityMeasure (Icc (1:ℝ) D.U))
    (v : ℝ) (price : Icc D.R D.Up) : ℝ :=
  if h : H0=H1 then
    let jj : Fin H0:=Fin.cast (by cases side <;> simp [AllCountAtypical.ownCount,h]) j
    ∫b,∫s,∫u : unitInterval,equalPrivateValue D A H0 jj e μP v price b s u
      ∂(volume : Measure unitInterval) ∂(SourceAmbientLaws.privateRaw D H0 e μP : Measure _)
      ∂(rowLaw A (SourceAmbientLaws.common D e μA) : Measure _)
  else
    ∫b,∫s,∫u : unitInterval,unequalPrivateValue D A H0 H1 side reg low j e v price b s u
      ∂(volume : Measure unitInterval)
      ∂(SourceAmbientLaws.privateRaw D (AllCountAtypical.ownCount H0 H1 side) e μP : Measure _)
      ∂(rowLaw A (SourceAmbientLaws.common D e μA) : Measure _)

lemma measurable_activeValue (A H0 H1 : ℕ) (reg low : Bool) (e : Noise D.eps)
    (μP : ProbabilityMeasure (Icc D.R D.Up)) (v : ℝ) (price : Icc (1:ℝ) D.U) :
    Measurable (fun z : (Fin A→ Icc (1:ℝ) D.B)×unitInterval=>
      activeValue D A H0 H1 reg low e μP v price z.1 z.2) := by
  let f : ((Fin A→ Icc (1:ℝ) D.B)×unitInterval) →
      ZeroNoiseActive.Parameters D H0 × ZeroNoiseActive.Sample D A (X:=Unit) :=
    fun z=>((e,SourceAmbientLaws.privateBayes D H0 e μP),((),z))
  have hf : Measurable f := (measurable_const.prodMk measurable_const).prodMk
    (measurable_const.prodMk measurable_id)
  have hm := (ZeroNoiseActive.measurable_payoff D A H0 H1 reg low
    (ContinuousMap.const Unit v) (ContinuousMap.const Unit price)).comp hf
  convert! hm using 1

lemma activeValue_bound (A H0 H1 : ℕ) (reg low : Bool) (e : Noise D.eps)
    (μP : ProbabilityMeasure (Icc D.R D.Up)) (v : ℝ) (price : Icc (1:ℝ) D.U)
    (b : Fin A→ Icc (1:ℝ) D.B) (u : unitInterval) :
    |activeValue D A H0 H1 reg low e μP v price b u|≤|v|+2*D.B :=
  ActivePhysicalPayoff.utility_bound _ v _ D.B D.eta
    ((by norm_num : (0:ℝ)≤1).trans (physical (by norm_num) D.hU _).2.1)
    (physical (by norm_num) D.hU _).2.2 D.heta0 D.heta1

lemma measurable_equalPrivateValue (A H : ℕ) (j : Fin H) (e : Noise D.eps)
    (μP : ProbabilityMeasure (Icc D.R D.Up)) (v : ℝ) (price : Icc D.R D.Up) :
    Measurable (fun z : (Fin A→ Icc (1:ℝ) D.B)×(Signal H D.R D.V×unitInterval)=>
      equalPrivateValue D A H j e μP v price z.1 z.2.1 z.2.2) := by
  let own : EqualZeroNoisePrivate.Own D v v:=(⟨v,le_rfl,le_rfl⟩,price)
  exact (EqualZeroNoisePrivate.measurable_payoff D A H v v j (ContinuousMap.const _ price)).comp
    (by fun_prop : Measurable (fun z : (Fin A→ Icc (1:ℝ) D.B)×(Signal H D.R D.V×unitInterval)=>
      ((e,SourceAmbientLaws.privateBayes D H e μP),(own,z))))

lemma equalPrivateValue_bound (A H : ℕ) (j : Fin H) (e : Noise D.eps)
    (μP : ProbabilityMeasure (Icc D.R D.Up)) (v : ℝ) (price : Icc D.R D.Up)
    (b : Fin A→ Icc (1:ℝ) D.B) (s : Signal H D.R D.V) (u : unitInterval) :
    |equalPrivateValue D A H j e μP v price b s u|≤|v|+D.V := by
  have hp:=(physical D.hR D.hRUp (e,price,u)).2
  have hpV : (physical D.hR D.hRUp (e,price,u):ℝ)≤D.V := hp.2
  have hq:=PrivatePayoffContinuity.privateValue_bounds (c:=D.c) D.ξ j
    (fun i=>(SortedAllNoise.sortedBox b i:ℝ),policyMean A H D.c D.R D.V D.ξ 1 D.B
      (SortedAllNoise.sortedBox b,SourceAmbientLaws.privateBayes D H e μP),
      Function.update s j (Sum.inr (physical D.hR D.hRUp (e,price,u))))
  unfold equalPrivateValue
  rw [abs_mul,abs_of_nonneg hq.1]
  exact (mul_le_of_le_one_right (abs_nonneg _) hq.2).trans
    ((abs_sub _ _).trans (by rw [abs_of_nonneg (D.hR.le.trans hp.1)];linarith))

lemma measurable_unequalPrivateValue (A H0 H1 : ℕ) (side reg low : Bool)
    (j : Fin (AllCountAtypical.ownCount H0 H1 side)) (e : Noise D.eps)
    (v : ℝ) (price : Icc D.R D.Up) :
    Measurable (fun z : (Fin A→ Icc (1:ℝ) D.B)×
      (Signal (AllCountAtypical.ownCount H0 H1 side) D.R D.V×unitInterval)=>
      unequalPrivateValue D A H0 H1 side reg low j e v price z.1 z.2.1 z.2.2) := by
  let own : EqualZeroNoisePrivate.Own D v v:=(⟨v,le_rfl,le_rfl⟩,price)
  exact (UnequalZeroNoisePrivate.measurable_payoff D A H0 H1 side reg low v v j
    (ContinuousMap.const _ price)).comp
      (by fun_prop : Measurable (fun z : (Fin A→ Icc (1:ℝ) D.B)×
        (Signal (AllCountAtypical.ownCount H0 H1 side) D.R D.V×unitInterval)=>(e,(own,z))))

lemma unequalPrivateValue_bound (A H0 H1 : ℕ) (side reg low : Bool)
    (j : Fin (AllCountAtypical.ownCount H0 H1 side)) (e : Noise D.eps)
    (v : ℝ) (price : Icc D.R D.Up) (b : Fin A→ Icc (1:ℝ) D.B)
    (s : Signal (AllCountAtypical.ownCount H0 H1 side) D.R D.V) (u : unitInterval) :
    |unequalPrivateValue D A H0 H1 side reg low j e v price b s u|≤|v|+D.V := by
  have hw:=UnequalPartialCountPayoff.rawWeight_bounds A H0 H1 D.c D.ξ
    (D.U*(1+(e:ℝ))) D.R (D.Up*(1+(e:ℝ))) D.width (D.e0 reg) D.F reg low
    (D.marksLaw H0) (D.marksLaw H1) (fun i=>(b i:ℝ))
  have hr:=AtypicalPartialNoisy.rankInclusion_bounds A H0 H1 D.c side j
    ((physical D.hR D.hRUp (e,price,u):ℝ),s)
  have hp:=(physical D.hR D.hRUp (e,price,u)).2
  have hpV : (physical D.hR D.hRUp (e,price,u):ℝ)≤D.V := hp.2
  let w:=UnequalPartialCountPayoff.rawWeight A H0 H1 D.c D.ξ
    (D.U*(1+(e:ℝ))) D.R (D.Up*(1+(e:ℝ))) D.width (D.e0 reg) D.F reg low
    (D.marksLaw H0) (D.marksLaw H1) (fun i=>(b i:ℝ))
  rcases hw with ⟨hw0,hw1⟩
  have hi : w*(if reg then 0 else 1)+(1-w)*AtypicalPartialNoisy.rankInclusion A H0 H1 D.c
      side j ((physical D.hR D.hRUp (e,price,u):ℝ),s)∈Icc (0:ℝ) 1 := by
    cases reg <;> simp only [Bool.false_eq_true,ite_false,ite_true,mul_zero,mul_one,zero_add] <;>
      constructor <;> dsimp only [w] at * <;> nlinarith
  unfold unequalPrivateValue
  rw [abs_mul,abs_of_nonneg hi.1]
  exact (mul_le_of_le_one_right (abs_nonneg _) hi.2).trans
    ((abs_sub _ _).trans (by rw [abs_of_nonneg (D.hR.le.trans hp.1)];linarith))

end FCAppendix.Affine.Tail04.AmbientFiniteGame
