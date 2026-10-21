import FCAppendix.Affine.Uniform07Finishing.Crossover.Received05Menu
import FCAppendix.Affine.Uniform07Finishing.Native.Concrete05Zero

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing.Crossover.Received05
open MeasureTheory ProbabilityTheory Game Bayes Set Filter Topology Classical
open FCAppendix.Affine

structure ReadyLowerFamily extends Concrete05.LowerFamily where
  ready : ∀ row k,readyPredicate row (start+k) (construction row k).finite.restricted

theorem exists_ready_lower_family : Nonempty ReadyLowerFamily := by
  have hrow (row : Uniform07.Row) : ∀ᶠ m in atTop,
      Nonempty (UniformFinite.NativeFiniteLowerConstruction row m (sourceLowerPriceCeiling row)) ∧
      ∀E : UniformFinite.ExactRestrictedLaw row m,readyPredicate row m E := by
    obtain ⟨N,hN⟩:=UniformFinite.exists_eventual_uniform_lower_construction row
    filter_upwards [eventually_ge_atTop N,eventually_ready row] with m hm hr
    refine ⟨hN m hm _ ?_,hr⟩
    rw [Concrete05.cap_eq]
    exact (Physical.source_auxiliary_floor_guards row).2.1
  have hboth : ∀ᶠ m in atTop,∀row : Uniform07.Row,
      Nonempty (UniformFinite.NativeFiniteLowerConstruction row m (sourceLowerPriceCeiling row)) ∧
      ∀E : UniformFinite.ExactRestrictedLaw row m,readyPredicate row m E := by
    filter_upwards [hrow Uniform07.Row.first,hrow Uniform07.Row.second] with m h₀ h₁ row
    cases row
    · exact h₀
    · exact h₁
  obtain ⟨N,hN⟩:=eventually_atTop.mp hboth
  let start:=max 3 N
  have htail (k : ℕ) (row : Uniform07.Row) := hN (start+k) (by dsimp [start]; omega) row
  let W (row : Uniform07.Row) (k : ℕ) := Classical.choice (htail k row).1
  exact ⟨{
    start:=start
    start_ge_three:=le_max_left _ _
    construction:=W
    ready:=fun row k=>(htail k row).2 (W row k).finite.restricted }⟩

def readyLowerFamily : ReadyLowerFamily:=Classical.choice exists_ready_lower_family

namespace ReadyLowerFamily

def law (F : ReadyLowerFamily) (row : Uniform07.Row) (k : ℕ) : ReadyLaw row (F.start+k) :=
  ⟨(F.construction row k).finite.restricted,F.ready row k⟩

abbrev market (F : ReadyLowerFamily) (row : Uniform07.Row) (k : ℕ) :
    UniformMarketData row (F.start+k) := F.toLowerFamily.marketData row k

theorem native_eq (F : ReadyLowerFamily) (row : Uniform07.Row) (k : ℕ) :
    letI : Nonempty (Fin (F.start+k)) := (F.market row k).fin_nonempty
    (F.market row k).native=
      Concrete05.nativeGame (F.law row k).1
        (F.market row k).capacity_positive (sourceLowerPriceCeiling row) := by
  rfl

end ReadyLowerFamily
end FCAppendix.Affine.Uniform07Finishing.Crossover.Received05
