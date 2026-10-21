import FCAppendix.Affine.EqualCapacityNative
import FCAppendix.Affine.Hybrid.SupportSampler

noncomputable section
namespace FCAppendix.Affine.Hybrid.NativeEqual
open MeasureTheory ProbabilityTheory Game Set Classical
open EqualCapacity
open Existence.PayOnceBounded (listBids measurable_listBids positiveSupport mem_positiveSupport)
open scoped BigOperators

private theorem exists_sample (m : ℕ) (ξ : ℝ) (hξ : 0<ξ) (hξ1 : ξ<1) (r : ℕ) :
    ∃f : LocalList m→unitInterval→Finset (Fin m),
      Measurable (Function.uncurry f) ∧
      (∀L s,0<(canonicalLottery ξ r (listBids L)).mass (f L s)) ∧
      ∀L,volume.map (f L)=FiniteLaw.probabilityMeasure (canonicalLottery ξ r (listBids L)) := by
  apply exists_support_sampler
  intro S
  exact (ExactCapacity.measurable_symmetricLottery_mass S).comp
    (measurable_listMarginal m ξ r hξ hξ1)

def sample (m : ℕ) (ξ : ℝ) (hξ : 0<ξ) (hξ1 : ξ<1) (r : ℕ) :
    LocalList m→unitInterval→Finset (Fin m):=(exists_sample m ξ hξ hξ1 r).choose

theorem measurable_sample (m : ℕ) (ξ : ℝ) (hξ : 0<ξ) (hξ1 : ξ<1) (r : ℕ) :
    Measurable (Function.uncurry (sample m ξ hξ hξ1 r)):=
  (exists_sample m ξ hξ hξ1 r).choose_spec.1

theorem sample_support (m : ℕ) (ξ : ℝ) (hξ : 0<ξ) (hξ1 : ξ<1) (r : ℕ)
    (L : LocalList m) (s : unitInterval) :
    0<(canonicalLottery ξ r (listBids L)).mass (sample m ξ hξ hξ1 r L s):=
  (exists_sample m ξ hξ hξ1 r).choose_spec.2.1 L s

theorem sample_law (m : ℕ) (ξ : ℝ) (hξ : 0<ξ) (hξ1 : ξ<1) (r : ℕ) (L : LocalList m) :
    volume.map (sample m ξ hξ hξ1 r L)=FiniteLaw.probabilityMeasure (canonicalLottery ξ r (listBids L)):=
  (exists_sample m ξ hξ hξ1 r).choose_spec.2.2 L

theorem sample_feasible (m : ℕ) (ξ : ℝ) (hξ : 0<ξ) (hξ1 : ξ<1) (r : ℕ)
    (L : LocalList m) (s : unitInterval) : LocallyFeasible L r (sample m ξ hξ hξ1 r L s) := by
  have hp:=positiveMarginal_spec ξ r hξ hξ1 (listBids L)
  apply symmetricLottery_support_locallyFeasible L (positiveMarginal ξ r (listBids L))
    (min r (positiveSupport (listBids L)).card) (min_le_left _ _) hp.1 hp.2.1 hp.2.2 _
    (sample m ξ hξ hξ1 r L s) (sample_support m ξ hξ hξ1 r L s).ne'
  intro i hi
  apply onSupport_outside
  rw [mem_positiveSupport]
  simp only [listBids,hi,Option.getD_none,lt_self_iff_false,not_false_eq_true]

theorem sample_optimal (m : ℕ) (ξ : ℝ) (hξ : 0<ξ) (hξ1 : ξ<1) (r : ℕ)
    (L : LocalList m) (s : unitInterval) :
    Finite.Optimal r (fun i=>listBids L i*(1-ξ*positiveMarginal ξ r (listBids L) i))
      (sample m ξ hξ hξ1 r L s):=
  canonicalLottery_support_optimal hξ hξ1 r (listBids L) _ (sample_support m ξ hξ hξ1 r L s).ne'

theorem sample_acceptance (m : ℕ) (ξ : ℝ) (hξ : 0<ξ) (hξ1 : ξ<1) (r : ℕ)
    (L : LocalList m) (i : Fin m) :
    (∫s : unitInterval,if i∈sample m ξ hξ hξ1 r L s then (1:ℝ) else 0)=
      positiveMarginal ξ r (listBids L) i := by
  have hm : Measurable (sample m ξ hξ hξ1 r L):=
    (measurable_sample m ξ hξ hξ1 r).comp (measurable_const.prodMk measurable_id)
  have hLaw:=FiniteLaw.ofMeasure_eq_of_map_eq_probabilityMeasure volume _ hm
    (canonicalLottery ξ r (listBids L)) (sample_law m ξ hξ hξ1 r L)
  have hi:=(canonicalLottery_implements hξ hξ1 r (listBids L)).2 i
  rw [←hLaw,FiniteLaw.prob_eq_expect,FiniteLaw.expect_ofMeasure] at hi
  exact hi

theorem measurable_sample_capacity (m : ℕ) (ξ : ℝ) (hξ : 0<ξ) (hξ1 : ξ<1) :
    Measurable (fun x : ℕ×(LocalList m×unitInterval)=>sample m ξ hξ hξ1 x.1 x.2.1 x.2.2):=
  measurable_from_prod_countable_right (fun r=>measurable_sample m ξ hξ hξ1 r)

end FCAppendix.Affine.Hybrid.NativeEqual
