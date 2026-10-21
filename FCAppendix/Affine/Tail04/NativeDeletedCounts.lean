import FCAppendix.Affine.Tail04.OriginalFiniteFibers
import FCAppendix.Probability.FinitePushforward
import FCAppendix.Game.JointMeasurability

noncomputable section
namespace FCAppendix.Affine.Tail04.NativeDeletedCounts
open MeasureTheory ProbabilityTheory Set Classical Game Bayes Hybrid
open OriginalFiniteFibers
open scoped BigOperators

variable {N c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

def dummyDraw : UserDraw 2 := ((0,Interim.abstain 2),Equiv.refl (Fin 2))

def restoreUsers (i : Fin (N+1)) (r : Fin N → UserDraw 2) : UserProfile (N+1) 2 :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N+1) => UserDraw 2) i).symm (dummyDraw,r)

lemma measurable_restoreUsers (i : Fin (N+1)) : Measurable (restoreUsers i) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N+1) => UserDraw 2) i).symm.measurable.comp
    (measurable_const.prodMk measurable_id)

lemma restoreUsers_delete (i : Fin (N+1)) (r : UserProfile (N+1) 2) :
    restoreUsers i (NativeFlag.deletedUsers i r)=Function.update r i dummyDraw := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N+1) => UserDraw 2) i
  apply e.injective
  change e (e.symm (dummyDraw,NativeFlag.deletedUsers i r))=e (Function.update r i dummyDraw)
  rw [e.apply_symm_apply]
  apply Prod.ext
  · change dummyDraw=(Function.update r i dummyDraw) i
    simp
  · funext j
    change r (i.succAbove j)=(Function.update r i dummyDraw) (i.succAbove j)
    simp

def restoreSample (i : Fin (N+1)) (z : DeletedSample N Seed) : Sample (N+1) 2 Seed :=
  ((restoreUsers i z.1.1,z.1.2),z.2)

lemma measurable_restoreSample (i : Fin (N+1)) :
    Measurable (restoreSample (Seed:=Seed) i) :=
  (((measurable_restoreUsers i).comp (measurable_fst.comp measurable_fst)).prodMk
    (measurable_snd.comp measurable_fst)).prodMk measurable_snd

omit [MeasurableSpace Seed] in
lemma observed_restore_delete (i : Fin (N+1)) (a : JointAction 2)
    (ω : Sample (N+1) 2 Seed) (j : Fin 2) :
    observe (deviated i a (restoreSample i (deleteSample i ω))) j=
      observe (deviated i a ω) j := by
  change observe (deviated i a ((restoreUsers i (NativeFlag.deletedUsers i ω.1.1),ω.1.2),ω.2)) j=_
  rw [restoreUsers_delete]
  funext k
  by_cases hk : k=i
  · subst k
    simp only [observe,deviated_recipients_self,deviated_bid_self]
  · simp only [observe,deviated_recipients_other i k hk,deviated_bid_other i k hk,
      Function.update_of_ne hk]

lemma focalCount_restore_delete (Γ : FiniteGame (N+1) 2 c Seed)
    (i : Fin (N+1)) (a : JointAction 2) (ω : Sample (N+1) 2 Seed) :
    focalCount Γ i a (restoreSample i (deleteSample i ω))=focalCount Γ i a ω := by
  apply Fin.ext
  change inclusionCount _ Γ.policy _ i=inclusionCount _ Γ.policy _ i
  rw [inclusionCount_eq_sum,inclusionCount_eq_sum]
  apply Finset.sum_congr rfl
  intro j _
  have he := congrArg (fun L => (Γ.policy j L (ω.1.2 j)).val)
    (observed_restore_delete i a ω j)
  change (if i∈(Γ.policy j _ (ω.1.2 j)).val then 1 else 0)=
    (if i∈(Γ.policy j _ (ω.1.2 j)).val then 1 else 0)
  rw [he]

def deletedCount (Γ : FiniteGame (N+1) 2 c Seed) (i : Fin (N+1)) (a : JointAction 2) :
    DeletedSample N Seed → Fin 3 := fun z => focalCount Γ i a (restoreSample i z)

lemma measurable_deletedCount (Γ : FiniteGame (N+1) 2 c Seed)
    (i : Fin (N+1)) (a : JointAction 2) : Measurable (deletedCount Γ i a) :=
  (measurable_focalCount Γ i a).comp (measurable_restoreSample i)

theorem raw_count_measure (Γ : FiniteGame (N+1) 2 c Seed)
    (i : Fin (N+1)) (a : JointAction 2) :
    (sampleLaw Γ).map (focalCount Γ i a)=
      (deletedSampleLaw Γ).map (deletedCount Γ i a) := by
  have h := deleteSample_preserves Γ i
  calc
    _ = (sampleLaw Γ).map ((deletedCount Γ i a) ∘ deleteSample i) := by
      apply Measure.map_congr
      exact Filter.Eventually.of_forall (fun ω => (focalCount_restore_delete Γ i a ω).symm)
    _ = ((sampleLaw Γ).map (deleteSample i)).map (deletedCount Γ i a) :=
      (Measure.map_map (measurable_deletedCount Γ i a) h.measurable).symm
    _ = _ := by rw [h.map_eq]

theorem raw_count_law (Γ : FiniteGame (N+1) 2 c Seed)
    (i : Fin (N+1)) (a : JointAction 2) :
    (problem Γ i).outcome a=FiniteLaw.ofMeasure (deletedSampleLaw Γ)
      (deletedCount Γ i a) (measurable_deletedCount Γ i a) := by
  rw [problem_outcome]
  have he : CountLaw.ofMeasure (sampleLaw Γ) (focalCount Γ i a) (measurable_focalCount Γ i a) =
      FiniteLaw.ofMeasure (sampleLaw Γ) (focalCount Γ i a) (measurable_focalCount Γ i a) := by
    apply FiniteLaw.ext_expect
    intro f
    rw [CountLaw.expect_ofMeasure, FiniteLaw.expect_ofMeasure]
  rw [he]
  exact FiniteLaw.ofMeasure_eq_of_map_eq (sampleLaw Γ) (deletedSampleLaw Γ)
    (focalCount Γ i a) (measurable_focalCount Γ i a)
    (deletedCount Γ i a) (measurable_deletedCount Γ i a) (raw_count_measure Γ i a)

theorem native_count_finite_fibers (Γ : FiniteGame (N+1) 2 c Seed)
    {K : Type*} [Fintype K] [MeasurableSpace K] [MeasurableSingletonClass K]
    (tag : UserDraw 2 → K) (htag : Measurable tag)
    (i : Fin (N+1)) (a : JointAction 2) :
    (sampleLaw Γ).map (focalCount Γ i a)=
      ∑ k : Fin N → K,(∏ j,userLaw Γ (tag ⁻¹' {k j})) •
        ((((Measure.pi (fun j => cond (userLaw Γ) (tag ⁻¹' {k j}))).prod
          (Measure.pi (fun _ : Fin 2 => Γ.seedLaw))).prod (permLaw 2)).map (deletedCount Γ i a)) := by
  rw [raw_count_measure]
  exact deletedSample_map_fibers Γ tag htag _ (measurable_deletedCount Γ i a)

end FCAppendix.Affine.Tail04.NativeDeletedCounts
