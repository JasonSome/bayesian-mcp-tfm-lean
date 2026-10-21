import FCAppendix.Existence.R01PayOnceMixedGame
import FCAppendix.Exclusive.SourceLowTypeCount
import FCAppendix.PayOnce.InterimCountTransport

noncomputable section
namespace FCAppendix.Bayes.PayOnceConstruction
open MeasureTheory ProbabilityTheory Game Set Filter
open Existence.PayOnceBounded
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {m n c : ℕ} (hn : 2≤n) (F : Measure ℝ) [IsProbabilityMeasure F]
    {W : ℝ} (κ : Kernel ℝ (FloorAction 0 W)) [IsMarkovKernel κ]
    (G : Schedule n) (g : ℝ) (hg : 0≤g)
local notation "Gamma"=>mixedGame m n c hn F κ G g hg

theorem mixedGame_value_action_law : (Gamma).F ⊗ₘ (Gamma).σ=
    (F ⊗ₘ κ).map (Prod.map id (nativeAction n)) :=
  Measure.compProd_map (measurable_nativeAction n W)

theorem mixedGame_seedLottery_marginal (j : Fin n) (L : LocalList m) (i : Fin m) :
    Proposer.marginal (seedLottery Gamma j L) i=listMarginal n c L i := by
  rw [mixedGame_seedLottery]
  have hp:=positiveMarginal_spec n c hn (listBids L)
  exact (ExactCapacity.symmetricLottery_implements _ _ hp.1 hp.2.1 hp.2.2).2 i

def stateProfile (v : Fin m→ℝ) (s : Fin m→FloorAction 0 W)
    (τ : Fin m→Equiv.Perm (Fin n)) : UserProfile m n :=
  fun i=>((v i,nativeAction n (s i)),τ i)

def deviationList (s : Fin m→FloorAction 0 W) (i : Fin m) (b : ℝ) : LocalList m :=
  fun l=>if l=i then some b else match s l with
    | .inl _=>none
    | .inr bb=>some bb.1

theorem deviationList_bids (s : Fin m→FloorAction 0 W) (i : Fin m) (b : ℝ) :
    listBids (deviationList s i b)=Function.update (fun l=>bid (s l)) i b := by
  funext l
  by_cases h:l=i
  · subst l; simp [listBids,deviationList]
  · cases hs:s l <;> simp [listBids,deviationList,h,hs,bid]

theorem deviationList_common (v : Fin m→ℝ) (s : Fin m→FloorAction 0 W)
    (τ : Fin m→Equiv.Perm (Fin n)) (i : Fin m) (a : JointAction n)
    (η : Equiv.Perm (Fin n)) (j : Fin n)
    (hj : j∈(drawsRealization (Function.update (stateProfile v s τ) i ((0,a),η))).recipients i) :
    observe (drawsRealization (Function.update (stateProfile v s τ) i ((0,a),η))) j=
      deviationList s i a.bid := by
  have hji : j∈firstK η a.routeCount := by simpa [drawsRealization] using hj
  funext l
  by_cases h:l=i
  · subst l
    simp [observe,drawsRealization,hji,deviationList]
  · cases hs:s l with
    | inl u=>simp [observe,drawsRealization,stateProfile,nativeAction,Interim.abstain,
        deviationList,h,hs,mem_firstK]
    | inr bb=>simp [observe,drawsRealization,stateProfile,nativeAction,
        deviationList,h,hs,mem_firstK]

theorem mixedGame_profile_count_test (v : Fin m→ℝ) (s : Fin m→FloorAction 0 W)
    (τ : Fin m→Equiv.Perm (Fin n)) (i : Fin m) (a : JointAction n)
    (η : Equiv.Perm (Fin n)) (f : ℕ→ℝ) :
    (profileCountLaw Gamma (Function.update (stateProfile v s τ) i ((0,a),η)) i).expect
      (fun r=>f r.val)=Exclusive.Narrow.binomialPolynomial a.routeCount f
        (positiveMarginal n c (Function.update (fun l=>bid (s l)) i a.bid) i) := by
  let j : Fin n:=⟨0,by omega⟩
  let L:=deviationList s i a.bid
  let μ:=seedLottery Gamma j L
  have hs:=mixedGame_symmetric_at_list (m:=m) (c:=c) hn F κ G g hg j L
  have ht:=ExclusiveSource.profile_test_of_recipient_common_list Gamma
    (Function.update (stateProfile v s τ) i ((0,a),η)) i L
    (fun j hj=>deviationList_common v s τ i a η j hj) μ hs f
  have hcard : ((drawsRealization
      (Function.update (stateProfile v s τ) i ((0,a),η))).recipients i).card=a.routeCount := by
    simp only [drawsRealization,Function.update_self]
    exact card_firstK η a.routeCount a.routeCount_le
  rw [hcard,mixedGame_seedLottery_marginal] at ht
  simpa only [L,listMarginal,deviationList_bids] using ht

theorem mixedGame_profile_success (v : Fin m→ℝ) (s : Fin m→FloorAction 0 W)
    (τ : Fin m→Equiv.Perm (Fin n)) (i : Fin m) (a : JointAction n)
    (η : Equiv.Perm (Fin n)) :
    (profileCountLaw Gamma (Function.update (stateProfile v s τ) i ((0,a),η)) i).success=
      PayOnce.success a.routeCount
        (positiveMarginal n c (Function.update (fun l=>bid (s l)) i a.bid) i) := by
  change (profileCountLaw Gamma _ i).expect (fun r=>successIndicator r.val)=_
  rw [mixedGame_profile_count_test hn F κ G g hg v s τ i a η successIndicator,
    Exclusive.Narrow.binomialPolynomial_once]

end FCAppendix.Bayes.PayOnceConstruction
