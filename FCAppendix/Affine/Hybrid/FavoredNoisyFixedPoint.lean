import FCAppendix.Affine.Hybrid.FavoredNoisyPayoff
import FCAppendix.Existence.R01Parameterization
import FCAppendix.Existence.R01CompactProduct

noncomputable section
namespace FCAppendix.Affine.Hybrid
open MeasureTheory ProbabilityTheory Set Filter Topology
open Existence.Distributional
open scoped BigOperators

abbrev ActiveValue (vlo vhi : ℝ) := Icc vlo vhi
abbrev ActiveBaseBid (L U : ℝ) := Icc L U
abbrev ActivePhysicalBid (L U eps : ℝ) := Icc L (U*(1+eps))

def activeNoisyBid {vlo vhi L U eps : ℝ} (hL : 0<L) (heps : 0≤eps)
    (t : (ActiveValue vlo vhi × ActiveBaseBid L U) × unitInterval) : ActivePhysicalBid L U eps :=
  ⟨activeNoisyRealBid eps t.1.2 t.2,activeNoisyRealBid_mem hL heps t.1.2 t.2⟩

lemma continuous_activeNoisyBid {vlo vhi L U eps : ℝ} (hL : 0<L) (heps : 0≤eps) :
    Continuous (activeNoisyBid (vlo:=vlo) (vhi:=vhi) (U:=U) hL heps) := by
  apply Continuous.subtype_mk
  unfold activeNoisyRealBid
  fun_prop

def activeNoisyLaw {vlo vhi L U eps : ℝ} (hL : 0<L) (heps : 0≤eps)
    (mu : Measure (ActiveValue vlo vhi)) [IsProbabilityMeasure mu]
    (pi : Law (A:=ActiveBaseBid L U) mu) : Law (A:=ActivePhysicalBid L U eps) mu :=
  noisyLaw mu (⟨volume,inferInstance⟩ : ProbabilityMeasure unitInterval)
    (activeNoisyBid hL heps) (continuous_activeNoisyBid hL heps) pi

lemma continuous_activeNoisyLaw {vlo vhi L U eps : ℝ} (hL : 0<L) (heps : 0≤eps)
    (mu : Measure (ActiveValue vlo vhi)) [IsProbabilityMeasure mu] :
    Continuous (activeNoisyLaw (U:=U) hL heps mu) :=
  continuous_noisyLaw mu (⟨volume,inferInstance⟩ : ProbabilityMeasure unitInterval)
    (activeNoisyBid hL heps) (continuous_activeNoisyBid hL heps)

def activeImplementedBidLaw {vlo vhi L U eps : ℝ} (hL : 0<L) (heps : 0≤eps)
    (mu : Measure (ActiveValue vlo vhi)) [IsProbabilityMeasure mu]
    (pi : Law (A:=ActiveBaseBid L U) mu) : ProbabilityMeasure (ActivePhysicalBid L U eps) :=
  (activeNoisyLaw hL heps mu pi).1.map measurable_snd.aemeasurable

lemma continuous_activeImplementedBidLaw {vlo vhi L U eps : ℝ} (hL : 0<L) (heps : 0≤eps)
    (mu : Measure (ActiveValue vlo vhi)) [IsProbabilityMeasure mu] :
    Continuous (activeImplementedBidLaw (U:=U) hL heps mu) :=
  (ProbabilityMeasure.continuous_map continuous_snd).comp
    (continuous_subtype_val.comp (continuous_activeNoisyLaw hL heps mu))

def guardedRowInput {N : ℕ} {vlo vhi L U eps : ℝ} (hL : 0<L) (heps : 0≤eps)
    (t : (ActiveValue vlo vhi × ActiveBaseBid L U) × (Fin N→ActivePhysicalBid L U eps)) :
    GuardedNoiseInput (Fin (N+1)) vlo vhi L U eps :=
  (t.1,Fin.cons (activeNoisyBid hL heps (t.1,0)) t.2)

lemma continuous_guardedRowInput {N : ℕ} {vlo vhi L U eps : ℝ} (hL : 0<L) (heps : 0≤eps) :
    Continuous (guardedRowInput (N:=N) (vlo:=vlo) (vhi:=vhi) (U:=U) hL heps) := by
  apply continuous_fst.prodMk
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j=>?_) i
  · exact (continuous_activeNoisyBid hL heps).comp (continuous_fst.prodMk continuous_const)
  · exact (continuous_apply j).comp continuous_snd

def guardedRowSmoothedPayoff {N : ℕ} {vlo vhi L U eps : ℝ} (hL : 0<L) (heps : 0≤eps)
    (xi eta : ℝ) (r K1 K2 : ℕ)
    (t : (ActiveValue vlo vhi × ActiveBaseBid L U) × (Fin N→ActivePhysicalBid L U eps)) : ℝ :=
  guardedSmoothedPayoff xi eta eps r K1 K2 0 (guardedRowInput hL heps t)

lemma continuous_guardedRowSmoothedPayoff {N : ℕ} {vlo vhi L U eps : ℝ}
    (hL : 0<L) (heps : 0<eps) (xi eta : ℝ) (r K1 K2 : ℕ)
    (hN : 1≤N) (hK0 : 0<K1+K2) (hKN : K1+K2<N+1) :
    Continuous (guardedRowSmoothedPayoff (N:=N) (vlo:=vlo) (vhi:=vhi) (U:=U)
      hL heps.le xi eta r K1 K2) :=
  (continuous_guardedSmoothedPayoff hL heps xi eta r K1 K2 (0:Fin (N+1))
    (by simpa using hN) hK0 (by simpa using hKN)).comp (continuous_guardedRowInput hL heps.le)

def guardedNoisyExpectedUtility {N : ℕ} {vlo vhi L U eps : ℝ} (hL : 0<L) (heps : 0≤eps)
    (xi eta : ℝ) (r K1 K2 : ℕ) (mu : Measure (ActiveValue vlo vhi)) [IsProbabilityMeasure mu]
    (p : Law (A:=ActiveBaseBid L U) mu × (ActiveValue vlo vhi × ActiveBaseBid L U)) : ℝ :=
  ∫b : Fin N→ActivePhysicalBid L U eps,guardedRowSmoothedPayoff hL heps xi eta r K1 K2 (p.2,b)
    ∂(rowLaw N (activeImplementedBidLaw hL heps mu p.1) : Measure (Fin N→ActivePhysicalBid L U eps))

lemma continuous_guardedNoisyExpectedUtility {N : ℕ} {vlo vhi L U eps : ℝ}
    (hL : 0<L) (heps : 0<eps) (xi eta : ℝ) (r K1 K2 : ℕ)
    (hN : 1≤N) (hK0 : 0<K1+K2) (hKN : K1+K2<N+1)
    (mu : Measure (ActiveValue vlo vhi)) [IsProbabilityMeasure mu] :
    Continuous (guardedNoisyExpectedUtility (N:=N) (U:=U) hL heps.le xi eta r K1 K2 mu) := by
  have hf:=continuous_guardedRowSmoothedPayoff (vlo:=vlo) (vhi:=vhi) (U:=U)
    hL heps xi eta r K1 K2 hN hK0 hKN
  have hi:=continuous_law_integral (guardedRowSmoothedPayoff hL heps.le xi eta r K1 K2) hf
  exact hi.comp (continuous_snd.prodMk
    ((continuous_rowLaw N).comp ((continuous_activeImplementedBidLaw hL heps.le mu).comp continuous_fst)))

theorem exists_noisy_guarded_active_law {N : ℕ} {vlo vhi L U eps : ℝ}
    (hL : 0<L) (hLU : L≤U) (heps : 0<eps) (xi eta : ℝ) (r K1 K2 : ℕ)
    (hN : 1≤N) (hK0 : 0<K1+K2) (hKN : K1+K2<N+1)
    (mu : Measure (ActiveValue vlo vhi)) [IsProbabilityMeasure mu] :
    ∃(pi : Law (A:=ActiveBaseBid L U) mu)(sigma : Kernel (ActiveValue vlo vhi) (ActiveBaseBid L U)),
      IsMarkovKernel sigma ∧ mu⊗ₘsigma=(pi.1 : Measure (ActiveValue vlo vhi × ActiveBaseBid L U)) ∧
      (∀ᵐv ∂mu,∀ᵐB ∂sigma v,∀B' : ActiveBaseBid L U,
        guardedNoisyExpectedUtility (N:=N) hL heps.le xi eta r K1 K2 mu (pi,(v,B'))≤
          guardedNoisyExpectedUtility (N:=N) hL heps.le xi eta r K1 K2 mu (pi,(v,B))) := by
  letI : Nonempty (ActiveBaseBid L U):=⟨⟨L,le_rfl,hLU⟩⟩
  obtain ⟨pi,sigma,hmark,hdis,_hjoint,hopt⟩:=exists_symmetric_law (A:=ActiveBaseBid L U) mu
    (guardedNoisyExpectedUtility (N:=N) hL heps.le xi eta r K1 K2 mu)
    (continuous_guardedNoisyExpectedUtility hL heps xi eta r K1 K2 hN hK0 hKN mu)
  exact ⟨pi,sigma,hmark,hdis,hopt⟩

end FCAppendix.Affine.Hybrid
