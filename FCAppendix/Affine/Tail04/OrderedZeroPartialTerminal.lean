import FCAppendix.Affine.Tail04.OrderedNativePayoffPartialTerminal
import FCAppendix.Affine.Tail04.ZeroPrivateRegularity

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedZeroPartialTerminal
open MeasureTheory ProbabilityTheory Set Classical Game Bayes Hybrid
open NativeLocalPolicy NativePartialTerminal NativePartialExperiment NativeFiberEnumerations
open NativeActiveFiberCoordinates PartialNativeCoordinates NativeMenuReports
open EqualPrivateSignal EqualPrivateUpper PrivateRowSorting PrivatePayoffContinuity
open SortedAllNoise LocalHighCommon ZeroPrivatePermutation OrderedNativePayoffPartialTerminal

variable {N c : ℕ} (K : NativeLocalPolicy.Data (N+1) c) (i : Fin (N+1))
  (kind : Fin N→Fin 4) (Q : PublicScenario.Data) (μL : Measure ℝ)
  (hQ : ∀ A,K.publicChoice A=PublicScenario.localChoice K.E Q μL A)
  (ω : Background (N+1) 2 Seed)
  (hr : ∀r,NativeMenuReports.MenuAction K.E (ω.1 (i.succAbove r)).1.2)
  (hk : rivalKinds K.E i ω=kind)
set_option quotPrecheck false in
local notation "common" => commonRow K.E i kind (fun r=>ω.1 (i.succAbove r))
set_option quotPrecheck false in
local notation "rows" => (privateRowRaw K.E i kind 2 (fun r=>ω.1 (i.succAbove r)),
  privateRowRaw K.E i kind 3 (fun r=>ω.1 (i.succAbove r)))

include hQ hr hk in
theorem value_regular (side : Bool) (price : Icc K.E.R K.E.Rp)
    (low : Bool) (pub : unitInterval)
    (hs : seedOnList μL (K.E.roleList 0 (presentList ω i price (physical side)))=
      if low then some pub else none)
    (hgap : (1-K.ξ)*K.E.U<K.E.R)
    (hc : ∀h : Fin (N+2),∀q,EqualReceiptLaw.receipt (c:=c) (ξ:=K.ξ)
      (K.signalLaw h) (sortedBox common) q≠(price:ℝ))
    (hno : ∀l,l≠focalIndex K i kind side→
      numericalEntry (focalRow K i kind side price rows l)≠(price:ℝ)) (v : ℝ) :
    (v-price)*(if OrderedNativePayoffPartialTerminal.privateAccept K i side price ω then (1:ℝ) else 0)=
      OrderedNativePayoffPartialExperiment.value K (commonSize i kind)
        (ownTotal K i kind side) (otherTotal K i kind side) (physical side) Q low
        (focalIndex K i kind side) v price common (focalRow K i kind side price rows)
        pub (privateSeed side ω) := by
  let own := ownTotal K i kind side
  let other := otherTotal K i kind side
  let row := focalRow K i kind side price rows
  let j := focalIndex K i kind side
  let σ := focalPermutation K i kind ω side price
  have hj : row j=Sum.inr price := ZeroPartialTerminal.focalRow_self K i kind side price rows
  rw [reindexed_inclusion K i kind Q μL hQ ω hr hk side price low pub hs]
  by_cases h : OrderedHigherRoles.first (physical side) own.val other.val
  · have hreg : own=other→PrivatePayoffContinuity.policyInput (c:=c) (ξ:=K.ξ)
        (JoinedHighPolicy.equalParameter (publicParameter K (commonSize i kind) own other Q low common pub))
        (signal row)∈Regular K.ξ j := by
      intro _
      exact ZeroPrivateRegularity.regular_focal (K.E.d_nonneg.trans_lt K.E.d_lt_R)
        (sortedBox common) (K.signalLaw own) row j price hj (hc own) hno
    have he := zero_permutation_regular K (commonSize i kind) own other
      (publicParameter K (commonSize i kind) own other Q low common pub)
      row j price hj hreg hno hgap σ (Equiv.refl _) (privateSeed side ω)
    simpa only [OrderedNativePayoffPartialExperiment.value,
      OrderedNativePayoffPartialExperiment.inclusion,h,ite_true,
      NativePartialExperiment.inclusion,sampler_false,PrivatePartialSorting.reindexRow,
      Equiv.refl_symm,Equiv.refl_apply,σ,row,j,own,other]
        using! congrArg (fun x=>(v-price)*x) he
  · have hreg : ∀he : own.val=other.val,
        PrivatePayoffContinuity.policyInput (c:=c) (ξ:=K.ξ)
          (JoinedHighPolicy.equalParameter (publicParameter K (commonSize i kind) other own Q low common pub))
          (fun l=>signal row (Fin.cast he.symm l))∈Regular K.ξ (Fin.cast he j) := by
      intro he
      let row' := fun l=>row (Fin.cast he.symm l)
      have hj' : row' (Fin.cast he j)=Sum.inr price := by
        simpa only [row',Fin.cast_cast,Fin.cast_eq_self] using! hj
      have hn' : ∀l,l≠Fin.cast he j→numericalEntry (row' l)≠(price:ℝ) := by
        intro l hl
        apply hno (Fin.cast he.symm l)
        intro heq
        apply hl
        simpa only [Fin.cast_cast,Fin.cast_eq_self] using! congrArg (Fin.cast he) heq
      exact ZeroPrivateRegularity.regular_focal (K.E.d_nonneg.trans_lt K.E.d_lt_R)
        (sortedBox common) (K.signalLaw other) row' (Fin.cast he j) price hj' (hc other) hn'
    have he := one_permutation_regular K (commonSize i kind) other own
      (publicParameter K (commonSize i kind) other own Q low common pub)
      row j price hj hreg hno hgap σ (Equiv.refl _) (privateSeed side ω)
    simpa only [OrderedNativePayoffPartialExperiment.value,
      OrderedNativePayoffPartialExperiment.inclusion,h,ite_false,
      NativePartialExperiment.inclusion,sampler_true,PrivatePartialSorting.reindexRow,
      Equiv.refl_symm,Equiv.refl_apply,σ,row,j,own,other]
        using! congrArg (fun x=>(v-price)*x) he

end FCAppendix.Affine.Tail04.OrderedZeroPartialTerminal
