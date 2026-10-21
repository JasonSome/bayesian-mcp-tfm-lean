import FCAppendix.Affine.Tail04.OrderedNativePayoffPartial
import FCAppendix.Affine.Tail04.OrderedOriginalNoisySequence
import FCAppendix.Affine.Tail04.OrderedAtomBandCarrier

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedNativePayoffIC
open MeasureTheory ProbabilityTheory Set Classical Game Bayes Hybrid
open Existence.Distributional OriginalValues OriginalPopulation
open SourceTailNoisyFixedPoint OrderedOriginalNoisySequence OrderedNativeBandCarrierIC
open LatentSpeciesCalculus LatentNoisyPopulation

variable {D : FiniteTailNoisyGame.Data} {P : ValueParameters} {t : ℝ} {ht : P.M<t} {N : ℕ}
  (S : Sequence D P t ht N) (n : ℕ)
  (hdR : P.d0<(S.data n).R) (H : ℝ) (hBH : (S.data n).B<H)
  (πL : Law (A:=LowBody.LowValue P.d0) P.originalLowLaw)
  (upperBid : ℝ→ℝ) (hupperBid : Measurable upperBid) (hfloor : ∀v,t<v→H≤upperBid v)
  (hrare : (1-(S.data n).ξ)*(S.data n).B+(S.data n).ξ*(S.data n).B*((N+1:ℕ)*
    (tailMass P t/(partialMass+tailMass P t)))≤(S.data n).R)
  (cats : FiniteLaw (Fin 4))
  (L : LowBody.ActualAtomlessLowLimit N P.d0 (S.data n).ξ (S.data n).c cats P.originalLowLaw)
  (hL : πL=L.joint)
local notation "Dn" => S.data n
local notation "Γ" => OrderedNativeNoisySource.game Dn P t ht hdR H hBH πL (S.law n)
  upperBid hupperBid hfloor (N+1) hrare

include cats L hL

theorem native_all_action (i : Fin (N+1)) (k : Fin 3) :
    ∀ᵐx ∂(ProbabilityMeasure.toMeasure (Subtype.val (S.law n k))),∀b : Icc (bidLo D k) (bidHi D k),
      (∫u : unitInterval,(problem Γ i).payoff (x.1:ℝ)
        (physicalBandAction Dn P t k (x.1,b) u))≤
      ∫u : unitInterval,(problem Γ i).payoff (x.1:ℝ)
        (physicalBandAction Dn P t k x u) := by
  filter_upwards [S.optimal n k] with x hx
  intro b
  rw [OrderedNativePayoffPartial.all_species_payoff Dn P t ht hdR H hBH πL (S.law n)
      upperBid hupperBid hfloor N (by simpa only [Nat.cast_add,Nat.cast_one,tailMass] using hrare) cats L hL k i (x.1,b),
    OrderedNativePayoffPartial.all_species_payoff Dn P t ht hdR H hBH πL (S.law n)
      upperBid hupperBid hfloor N (by simpa only [Nat.cast_add,Nat.cast_one,tailMass] using hrare) cats L hL k i x]
  exact hx b

theorem integrated_band_IC (i : Fin (N+1)) (k : Fin 3)
    (dev : (Icc (valueLo P k) (valueHi P t k)×Icc (bidLo D k) (bidHi D k))→
      Icc (bidLo D k) (bidHi D k)) (hdev : Measurable dev) (J : Set ℝ) :
    (∫z,bandGain Dn P t ht πL (S.law n) upperBid hupperBid hdR H hBH hfloor N hrare
      i k dev z ∂(((((ProbabilityMeasure.toMeasure (Subtype.val (S.law n k))).restrict (typedCluster Dn P t k J)).prod
        (volume : Measure unitInterval)).prod (permLaw 2)).prod
          (background Dn P t ht πL (S.law n) upperBid hupperBid hdR H hBH hfloor N hrare)))≤0 :=
  integrated_band_IC_of_native_identity Dn P t ht πL (S.law n) upperBid hupperBid
    hdR H hBH hfloor N hrare i k dev hdev J
    (OrderedNativePayoffPartial.all_species_payoff Dn P t ht hdR H hBH πL (S.law n)
      upperBid hupperBid hfloor N (by simpa only [Nat.cast_add,Nat.cast_one,tailMass] using hrare) cats L hL k i)
    (S.optimal n k)

theorem original_carrier_IC (i : Fin (N+1)) (k : Fin 3)
    (b : Icc (bidLo D k) (bidHi D k)) (J : Set ℝ) (hJ : MeasurableSet J) :
    (∫z,OrderedAtomBandCarrier.rawGain Dn P t ht πL (S.law n) upperBid hupperBid
      hdR H hBH hfloor N hrare i k b ((bidLo_pos Dn k).le.trans b.2.1) z
        ∂((drawLaw Dn P t ht πL (S.law n) upperBid hupperBid).restrict (bandCluster k J)).prod
          (background Dn P t ht πL (S.law n) upperBid hupperBid hdR H hBH hfloor N hrare))≤0 :=
  OrderedAtomBandCarrier.original_noisy_carrier_IC Dn P t ht πL (S.law n) upperBid hupperBid
    hdR H hBH hfloor N hrare i k b J hJ
    (OrderedNativePayoffPartial.all_species_payoff Dn P t ht hdR H hBH πL (S.law n)
      upperBid hupperBid hfloor N (by simpa only [Nat.cast_add,Nat.cast_one,tailMass] using hrare) cats L hL k i)
    (S.optimal n k)

end FCAppendix.Affine.Tail04.OrderedNativePayoffIC
