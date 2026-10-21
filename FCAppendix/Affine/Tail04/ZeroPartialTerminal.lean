import FCAppendix.Affine.Tail04.NativePartialTerminal
import FCAppendix.Affine.Tail04.ZeroPrivatePermutation

noncomputable section
namespace FCAppendix.Affine.Tail04.ZeroPartialTerminal
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open NativeLocalPolicy NativePartialTerminal NativePartialExperiment NativeFiberEnumerations
open NativeActiveFiberCoordinates PartialNativeCoordinates NativeMenuReports
open EqualPrivateSignal EqualPrivateUpper PrivateRowSorting PrivatePayoffContinuity
open LocalHighCommon ZeroPrivatePermutation NativeObservationPair JoinedHighPolicy Hybrid

variable {N c : ℕ} (K : NativeLocalPolicy.Data (N+1) c) (i : Fin (N+1))
  (kind : Fin N→ Fin 4)

lemma focalRow_self (side : Bool) (price : Icc K.E.R K.E.Rp) (rows : Rows K i kind) :
    focalRow K i kind side price rows (focalIndex K i kind side)=Sum.inr price := by
  cases side <;> rfl

variable (Q : PublicScenario.Data) (μL : Measure ℝ)
  (hQ : ∀ A,K.publicChoice A=PublicScenario.localChoice K.E Q μL A)
  (ω : Background (N+1) 2 Seed)
  (hr : ∀ r,NativeMenuReports.MenuAction K.E (ω.1 (i.succAbove r)).1.2)
  (hk : rivalKinds K.E i ω=kind)

local notation "common" => commonRow K.E i kind (fun r=> (Prod.fst ω) (i.succAbove r))
local notation "rows" => (privateRowRaw K.E i kind 2 (fun r=> (Prod.fst ω) (i.succAbove r)),
  privateRowRaw K.E i kind 3 (fun r=> (Prod.fst ω) (i.succAbove r)))

include Q hQ hr hk in
theorem value_zero_regular (price : Icc K.E.R K.E.Rp) (low : Bool) (pub : unitInterval)
    (hs : seedOnList μL (K.E.roleList 0 (presentList ω i price 0))=
      if low then some pub else none)
    (hgap : (1-K.ξ)*K.E.U< K.E.R)
    (hreg : post0 K i kind false=post1 K i kind false→
      policyInput (c:=c) (ξ:=K.ξ)
        (equalParameter (publicParameter K (commonSize i kind)
          (post0 K i kind false) (post1 K i kind false) Q low common pub))
        (signal (focalRow K i kind false price rows))∈Regular K.ξ (focalIndex K i kind false))
    (hno : ∀ l,l≠focalIndex K i kind false→
      numericalEntry (focalRow K i kind false price rows l)≠(price:ℝ)) (v : ℝ) :
    (v-price)*(if privateAccept K i false price ω then (1:ℝ) else 0)=
      value K (commonSize i kind) (post0 K i kind false) (post1 K i kind false) Q
        false low (focalIndex K i kind false) v price common
        (focalRow K i kind false price rows) pub (privateSeed false ω) := by
  let σ := NativeFiberEnumerations.privatePermutation K.E (insert i (rivalSet i kind 2))
    (presentList ω i price 0) (focalFirst _ i (focal_not_mem_rivalSet i kind 2))
  have he := zero_permutation_regular K (commonSize i kind)
    (post0 K i kind false) (post1 K i kind false)
    (publicParameter K (commonSize i kind) (post0 K i kind false) (post1 K i kind false)
      Q low common pub)
    (focalRow K i kind false price rows) (focalIndex K i kind false) price
    (focalRow_self K i kind false price rows) hreg hno hgap σ (Equiv.refl _) (ω.2 0).1
  simp only [privateAccept,Bool.false_eq_true,ite_false]
  rw [zero_reindexed K i kind Q μL hQ ω hr hk price low pub hs]
  simpa only [value,NativePartialExperiment.inclusion,sampler_false,PrivatePartialSorting.reindexRow,
    Equiv.refl_symm,Equiv.refl_apply,privateSeed,ite_false,σ]
      using! congrArg (fun x=>(v-price)*x) he

include Q hQ hr hk in
theorem value_one_regular (price : Icc K.E.R K.E.Rp) (low : Bool) (pub : unitInterval)
    (hs : seedOnList μL (K.E.roleList 0 (presentList ω i price 1))=
      if low then some pub else none)
    (hgap : (1-K.ξ)*K.E.U< K.E.R)
    (hreg : ∀ he : (post1 K i kind true).val=(post0 K i kind true).val,
      policyInput (c:=c) (ξ:=K.ξ)
        (equalParameter (publicParameter K (commonSize i kind)
          (post0 K i kind true) (post1 K i kind true) Q low common pub))
        (fun l=> signal (focalRow K i kind true price rows) (Fin.cast he.symm l))∈
          Regular K.ξ (Fin.cast he (focalIndex K i kind true)))
    (hno : ∀ l,l≠focalIndex K i kind true→
      numericalEntry (focalRow K i kind true price rows l)≠(price:ℝ)) (v : ℝ) :
    (v-price)*(if privateAccept K i true price ω then (1:ℝ) else 0)=
      value K (commonSize i kind) (post0 K i kind true) (post1 K i kind true) Q
        true low (focalIndex K i kind true) v price common
        (focalRow K i kind true price rows) pub (privateSeed true ω) := by
  let σ := NativeFiberEnumerations.privatePermutation K.E (insert i (rivalSet i kind 3))
    (presentList ω i price 1) (focalFirst _ i (focal_not_mem_rivalSet i kind 3))
  have he := one_permutation_regular K (commonSize i kind)
    (post0 K i kind true) (post1 K i kind true)
    (publicParameter K (commonSize i kind) (post0 K i kind true) (post1 K i kind true)
      Q low common pub)
    (focalRow K i kind true price rows) (focalIndex K i kind true) price
    (focalRow_self K i kind true price rows) hreg hno hgap σ (Equiv.refl _) (ω.2 1).1
  simp only [privateAccept,ite_true]
  rw [one_reindexed K i kind Q μL hQ ω hr hk price low pub hs]
  simpa only [value,NativePartialExperiment.inclusion,sampler_true,PrivatePartialSorting.reindexRow,
    Equiv.refl_symm,Equiv.refl_apply,privateSeed,ite_true,σ]
      using! congrArg (fun x=>(v-price)*x) he

end FCAppendix.Affine.Tail04.ZeroPartialTerminal
