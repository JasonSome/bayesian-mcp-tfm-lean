import FCAppendix.Existence.R01PayOnceNativeCounts
import FCAppendix.Existence.R01PayOnceNativeSymmetry

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

theorem mixedGame_ae_shape : ∀ᵐ x ∂((Gamma).F ⊗ₘ (Gamma).σ),
    (x.2.routeCount=0 ∧ x.2.bid=0) ∨ x.2.routeCount=n := by
  rw [mixedGame_value_action_law]
  have hm : Measurable (fun x : ℝ × FloorAction 0 W=>(x.1,nativeAction n x.2)) :=
    measurable_fst.prodMk ((measurable_nativeAction n W).comp measurable_snd)
  apply (ae_map_iff hm.aemeasurable ?_).mpr
  · exact Filter.Eventually.of_forall fun x=>by
      cases x.2 with
      | inl u=>exact Or.inl ⟨rfl,rfl⟩
      | inr b=>exact Or.inr rfl
  · have hS : MeasurableSet {a : JointAction n | (a.routeCount=0 ∧ a.bid=0) ∨ a.routeCount=n} :=
      ((measurableSet_eq_fun (measurable_routeCount n) measurable_const).inter
        (measurableSet_eq_fun (measurable_bid n) measurable_const)).union
        (measurableSet_eq_fun (measurable_routeCount n) measurable_const)
    exact measurable_snd hS

theorem mixedGame_profile_shape : ∀ᵐ d ∂userProfileLaw Gamma,
    ∀i,( (d i).1.2.routeCount=0 ∧ (d i).1.2.bid=0) ∨ (d i).1.2.routeCount=n := by
  have hu : ∀ᵐ u ∂userLaw Gamma,
      (u.1.2.routeCount=0 ∧ u.1.2.bid=0) ∨ u.1.2.routeCount=n :=
    (measurePreserving_fst (μ:=(Gamma).F ⊗ₘ (Gamma).σ) (ν:=permLaw n)).quasiMeasurePreserving.ae
      (mixedGame_ae_shape hn F κ G g hg)
  exact ae_all_iff.mpr fun i=>
    (measurePreserving_eval (fun _ : Fin m=>userLaw Gamma) i).quasiMeasurePreserving.ae hu

def nativeDeviationList (d : UserProfile m n) (i : Fin m) (b : ℝ) : LocalList m :=
  fun l=>if l=i then some b else if (d l).1.2.routeCount=0 then none else some (d l).1.2.bid

include hn in
theorem nativeDeviationList_bids (d : UserProfile m n)
    (hd : ∀l,((d l).1.2.routeCount=0 ∧ (d l).1.2.bid=0) ∨ (d l).1.2.routeCount=n)
    (i : Fin m) (b : ℝ) :
    listBids (nativeDeviationList d i b)=Function.update (fun l=>(d l).1.2.bid) i b := by
  funext l
  by_cases h:l=i
  · subst l; simp [listBids,nativeDeviationList]
  · by_cases hz:(d l).1.2.routeCount=0
    · have hb : (d l).1.2.bid=0 := by
        rcases hd l with ha|ha
        · exact ha.2
        · omega
      simp [listBids,nativeDeviationList,h,hz,hb]
    · simp [listBids,nativeDeviationList,h,hz]

include hn in
theorem nativeDeviationList_common (d : UserProfile m n)
    (hd : ∀l,((d l).1.2.routeCount=0 ∧ (d l).1.2.bid=0) ∨ (d l).1.2.routeCount=n)
    (i : Fin m) (a : JointAction n) (η : Equiv.Perm (Fin n)) (j : Fin n)
    (hj : j∈(drawsRealization (Function.update d i ((0,a),η))).recipients i) :
    observe (drawsRealization (Function.update d i ((0,a),η))) j=nativeDeviationList d i a.bid := by
  have hji : j∈firstK η a.routeCount := by simpa [drawsRealization] using hj
  funext l
  by_cases h:l=i
  · subst l; simp [observe,drawsRealization,hji,nativeDeviationList]
  · rcases hd l with hz|hr
    · simp [observe,drawsRealization,nativeDeviationList,h,hz.1,mem_firstK]
    · have hn0 : n≠0:=by omega
      simp [observe,drawsRealization,nativeDeviationList,h,hr,hn0,mem_firstK]

theorem native_profile_success (d : UserProfile m n)
    (hd : ∀l,((d l).1.2.routeCount=0 ∧ (d l).1.2.bid=0) ∨ (d l).1.2.routeCount=n)
    (i : Fin m) (a : JointAction n) (η : Equiv.Perm (Fin n)) :
    (profileCountLaw Gamma (Function.update d i ((0,a),η)) i).success=
      PayOnce.success a.routeCount
        (positiveMarginal n c (Function.update (fun l=>(d l).1.2.bid) i a.bid) i) := by
  let j : Fin n:=⟨0,by omega⟩
  let L:=nativeDeviationList d i a.bid
  have ht:=ExclusiveSource.profile_test_of_recipient_common_list Gamma
    (Function.update d i ((0,a),η)) i L
    (fun j hj=>nativeDeviationList_common hn d hd i a η j hj)
    (seedLottery Gamma j L) (mixedGame_symmetric_at_list hn F κ G g hg j L) successIndicator
  have hcard : ((drawsRealization (Function.update d i ((0,a),η))).recipients i).card=a.routeCount := by
    simp only [drawsRealization,Function.update_self]
    exact card_firstK η a.routeCount a.routeCount_le
  rw [hcard,mixedGame_seedLottery_marginal] at ht
  simpa only [CountLaw.success,L,listMarginal,nativeDeviationList_bids hn d hd,
    Exclusive.Narrow.binomialPolynomial_once] using ht

end FCAppendix.Bayes.PayOnceConstruction

namespace FCAppendix.Bayes.PayOnceConstruction
open MeasureTheory ProbabilityTheory Game Set Filter
open Existence.PayOnceBounded
open scoped BigOperators
variable {N n c : ℕ} (hn : 2≤n) (F : Measure ℝ) [IsProbabilityMeasure F]
    {W : ℝ} (κ : Kernel ℝ (FloorAction 0 W)) [IsMarkovKernel κ]
    (G : Schedule n) (g : ℝ) (hg : 0≤g)
local notation "Gamma"=>mixedGame (N+1) n c hn F κ G g hg

def tailBids (d : UserProfile (N+1) n) : Fin N→ℝ:=fun j=>(d j.succ).1.2.bid

theorem tailBids_measurePreserving : MeasurePreserving (tailBids (N:=N) (n:=n))
    (userProfileLaw Gamma) (Measure.pi (fun _ : Fin N=>realBidLaw Gamma)) := by
  have htail := (measurePreserving_snd (μ:=userLaw Gamma)
    (ν:=Measure.pi (fun _ : Fin N=>userLaw Gamma))).comp
    (measurePreserving_piFinSuccAbove (fun _ : Fin (N+1)=>userLaw Gamma) 0)
  have hbid := measurePreserving_pi (fun _ : Fin N=>userLaw Gamma)
    (fun _ : Fin N=>realBidLaw Gamma)
    (fun _=>show MeasurePreserving (fun d : UserDraw n=>d.1.2.bid)
      (userLaw Gamma) (realBidLaw Gamma) from ⟨measurable_drawBid,rfl⟩)
  convert hbid.comp htail using 1 <;> rfl

theorem mixedGame_interim_success (i : Fin (N+1)) (a : JointAction n) :
    ((problem Gamma i).outcome a).success=
      ∫r : Fin N→ℝ,PayOnce.success a.routeCount
        (positiveMarginal n c (Fin.cons a.bid r) 0)
        ∂Measure.pi (fun _ : Fin N=>realBidLaw Gamma) := by
  rw [mixedGame_outcome_eq hn F κ G g hg i 0]
  change ((problem Gamma 0).outcome a).expect (fun z=>successIndicator z.val)=_
  rw [interim_expect_eq_profile_update Gamma 0 (0,a)]
  have hm : Measurable (fun r : Fin N→ℝ=>PayOnce.success a.routeCount
      (positiveMarginal n c (Fin.cons a.bid r) 0)) :=
    (PayOnce.continuous_success a.routeCount).measurable.comp
      ((measurable_pi_apply 0).comp ((measurable_positiveMarginal n c hn).comp
        (measurable_pi_iff.mpr (fun j=>by
          refine Fin.cases ?_ (fun k=>?_) j
          · exact measurable_const
          · exact measurable_pi_apply k))))
  have hmap:=tailBids_measurePreserving (N:=N) (c:=c) hn F κ G g hg
  have he (η : Equiv.Perm (Fin n)) :
      (∫d,(profileCountLaw Gamma (Function.update d 0 ((0,a),η)) 0).expect
        (fun z=>successIndicator z.val) ∂userProfileLaw Gamma)=
      ∫r : Fin N→ℝ,PayOnce.success a.routeCount (positiveMarginal n c (Fin.cons a.bid r) 0)
        ∂Measure.pi (fun _ : Fin N=>realBidLaw Gamma) := by
    calc
      _=∫d,PayOnce.success a.routeCount (positiveMarginal n c (Fin.cons a.bid (tailBids d)) 0)
          ∂userProfileLaw Gamma := by
        apply integral_congr_ae
        filter_upwards [mixedGame_profile_shape hn F κ G g hg] with d hd
        have ht:=native_profile_success (c:=c) hn F κ G g hg d hd 0 a η
        have hv : Function.update (fun l=>(d l).1.2.bid) 0 a.bid=Fin.cons a.bid (tailBids d) := by
          funext j
          refine Fin.cases ?_ (fun k=>?_) j <;> simp [tailBids]
        simpa only [CountLaw.success,hv] using ht
      _=_ := by
        rw [←hmap.map_eq]
        exact (integral_map hmap.measurable.aemeasurable hm.aestronglyMeasurable).symm
  simp_rw [he]
  simp

end FCAppendix.Bayes.PayOnceConstruction
