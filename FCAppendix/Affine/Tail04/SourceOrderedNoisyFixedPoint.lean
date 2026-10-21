import FCAppendix.Affine.Tail04.OrderedFiniteTailNoisyGame
import FCAppendix.Affine.Tail04.SourceTailNoisyFixedPoint

noncomputable section
namespace FCAppendix.Affine.Tail04.SourceOrderedNoisyFixedPoint
open MeasureTheory ProbabilityTheory Set Filter Topology Classical
open Existence.Distributional OriginalValues FiniteTailNoisyGame CompactSourceBidLaws Hybrid
open SourceTailNoisyFixedPoint
open scoped BigOperators

def payoff (D : Data) (P : ValueParameters) (t : ℝ) (ht : P.M< t) (N : ℕ) :
    ∀ i : Fin 3,JointProfile D P t ht×
      (ActiveValue (valueLo P i) (valueHi P t i)×ActiveBaseBid (bidLo D i) (bidHi D i)) → ℝ := by
  intro i
  refine Fin.cases ?_ (fun j=>Fin.cases ?_ (fun k=>Fin.cases ?_ (fun n=>Fin.elim0 n) k) j) i
  · exact fun p => OrderedFiniteTailNoisyGame.activeExpected (installOriginal D P t ht) N
      (bidLaws D P t ht p.1,((p.2.1:ℝ),extendBid D.huU p.2.2))
  · exact fun p => OrderedFiniteTailNoisyGame.activeExpected (installOriginal D P t ht) N
      (bidLaws D P t ht p.1,((p.2.1:ℝ),p.2.2))
  · exact fun p => OrderedFiniteTailNoisyGame.partialExpected (installOriginal D P t ht) N
      (bidLaws D P t ht p.1,((p.2.1:ℝ),p.2.2))

theorem continuous_payoff (D : Data) (P : ValueParameters) (t : ℝ) (ht : P.M< t) (N : ℕ) (i : Fin 3) :
    Continuous (payoff D P t ht N i) := by
  have hi : i=0 ∨ i=1 ∨ i=2 := by omega
  rcases hi with hi | hi | hi <;> subst i
  · exact (OrderedFiniteTailNoisyGame.continuous_activeExpected (installOriginal D P t ht) N).comp
      (((continuous_bidLaws D P t ht).comp continuous_fst).prodMk
        ((continuous_subtype_val.comp (continuous_fst.comp continuous_snd)).prodMk
          ((continuous_extendBid D.huU).comp (continuous_snd.comp continuous_snd))))
  · exact (OrderedFiniteTailNoisyGame.continuous_activeExpected (installOriginal D P t ht) N).comp
      (((continuous_bidLaws D P t ht).comp continuous_fst).prodMk
        ((continuous_subtype_val.comp (continuous_fst.comp continuous_snd)).prodMk
          (continuous_snd.comp continuous_snd)))
  · exact (OrderedFiniteTailNoisyGame.continuous_partialExpected (installOriginal D P t ht) N).comp
      (((continuous_bidLaws D P t ht).comp continuous_fst).prodMk
        ((continuous_subtype_val.comp (continuous_fst.comp continuous_snd)).prodMk
          (continuous_snd.comp continuous_snd)))

theorem exists_original_joint_noisy_law (D : Data) (P : ValueParameters) (t : ℝ) (ht : P.M< t) (N : ℕ) :
    ∃ (π : JointProfile D P t ht)
      (σ : ∀ i : Fin 3,Kernel (ActiveValue (valueLo P i) (valueHi P t i))
        (ActiveBaseBid (bidLo D i) (bidHi D i))),
      (∀ i,IsMarkovKernel (σ i)) ∧
      (∀ i,originalValueLaw P t ht i ⊗ₘ σ i=((π i).1 : Measure _)) ∧
      (∀ i,AllActionOptimal (π i) (fun x => payoff D P t ht N i (π,x))) ∧
      (∀ i,∀ᵐ v ∂originalValueLaw P t ht i,∀ᵐ b ∂σ i v,
        ∀ b' : ActiveBaseBid (bidLo D i) (bidHi D i),
          payoff D P t ht N i (π,(v,b'))≤ payoff D P t ht N i (π,(v,b))) :=
  exists_population_laws (fun i => ActiveValue (valueLo P i) (valueHi P t i))
    (fun i => ActiveBaseBid (bidLo D i) (bidHi D i)) (originalValueLaw P t ht)
      (payoff D P t ht N) (continuous_payoff D P t ht N)

def sequencePayoff (D : Data) (P : ValueParameters) (t : ℝ) (ht : P.M< t) (N : ℕ)
    (eps : unitInterval) : ∀ i : Fin 3,JointProfile D P t ht×
      (ActiveValue (valueLo P i) (valueHi P t i)×ActiveBaseBid (bidLo D i) (bidHi D i)) → ℝ :=
  if h : 0<(eps:ℝ) ∧ (eps:ℝ)< D.eps then payoff (atNoise D eps h.1 h.2) P t ht N else fun _ _ => 0

lemma sequencePayoff_eq (D : Data) (P : ValueParameters) (t : ℝ) (ht : P.M< t) (N : ℕ)
    (eps : unitInterval) (heps : 0<(eps:ℝ)) (hsmall : (eps:ℝ)< D.eps) :
    sequencePayoff D P t ht N eps=payoff (atNoise D eps heps hsmall) P t ht N := by
  unfold sequencePayoff
  rw [dif_pos (show 0<(eps:ℝ) ∧ (eps:ℝ)<D.eps from ⟨heps,hsmall⟩)]

lemma continuous_sequencePayoff (D : Data) (P : ValueParameters) (t : ℝ) (ht : P.M< t) (N : ℕ)
    (eps : unitInterval) (i : Fin 3) : Continuous (sequencePayoff D P t ht N eps i) := by
  unfold sequencePayoff
  split_ifs with h
  · exact continuous_payoff (atNoise D eps h.1 h.2) P t ht N i
  · exact continuous_const

theorem exists_original_joint_noisy_sequence (D : Data) (hbudget : D.eps≤1)
    (P : ValueParameters) (t : ℝ) (ht : P.M< t) (N : ℕ) :
    ∃ (eps : ℕ → unitInterval) (π : ℕ → JointProfile D P t ht) (π₀ : JointProfile D P t ht),
      (∀ j,0<(eps j:ℝ) ∧ (eps j:ℝ)< D.eps) ∧
      Tendsto eps atTop (𝓝 0) ∧
      (∀ j,∃ σ : ∀ i : Fin 3,Kernel (ActiveValue (valueLo P i) (valueHi P t i))
          (ActiveBaseBid (bidLo D i) (bidHi D i)),
        (∀ i,IsMarkovKernel (σ i)) ∧
        (∀ i,originalValueLaw P t ht i ⊗ₘ σ i=((π j i).1 : Measure _)) ∧
        (∀ i,AllActionOptimal (π j i) (fun x => sequencePayoff D P t ht N (eps j) i (π j,x))) ∧
        (∀ i,∀ᵐ v ∂originalValueLaw P t ht i,∀ᵐ b ∂σ i v,
          ∀ b' : ActiveBaseBid (bidLo D i) (bidHi D i),
            sequencePayoff D P t ht N (eps j) i (π j,(v,b'))≤
              sequencePayoff D P t ht N (eps j) i (π j,(v,b)))) ∧
      Tendsto π atTop (𝓝 π₀) ∧
      (∀ i,Tendsto (fun j => activeUniversalNoisyLaw (bidLo_pos D i) (bidLo_le_hi D i)
          (originalValueLaw P t ht i) (eps j,π j i)) atTop
        (𝓝 (activeUniversalNoisyLaw (bidLo_pos D i) (bidLo_le_hi D i)
          (originalValueLaw P t ht i) (0,π₀ i)))) :=
  exists_joint_noisy_compact_sequence (valueLo P) (valueHi P t) (bidLo D) (bidHi D)
    (bidLo_pos D) (bidLo_le_hi D) (originalValueLaw P t ht)
    (sequencePayoff D P t ht N)
    (fun eps _ i => continuous_sequencePayoff D P t ht N eps i) D.eps D.heps hbudget

end FCAppendix.Affine.Tail04.SourceOrderedNoisyFixedPoint
