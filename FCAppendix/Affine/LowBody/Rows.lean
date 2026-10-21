import FCAppendix.Affine.ResidualPotential
import Mathlib.MeasureTheory.Constructions.Pi

noncomputable section
namespace FCAppendix.Affine.LowBody
open MeasureTheory Game Set
open scoped BigOperators ENNReal

abbrev RowRival := Fin 4 × ℝ

def rivalLaw (s a h : ℝ) (G : Measure ℝ) : Measure RowRival :=
  ENNReal.ofReal s • G.map (fun b=>(0,b)) +
  ENNReal.ofReal a • Measure.dirac (1,0) +
  ENNReal.ofReal (h/2) • Measure.dirac (2,0) +
  ENNReal.ofReal (h/2) • Measure.dirac (3,0)

theorem rivalLaw_isProbability (s a h : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ a) (hh : 0 ≤ h)
    (hsum : s + a + h=1) (G : Measure ℝ) [IsProbabilityMeasure G] :
    IsProbabilityMeasure (rivalLaw s a h G) := by
  constructor
  have hlow : Measurable (fun b : ℝ=>((0:Fin 4),b)) := measurable_const.prodMk measurable_id
  have ht : s + a + h/2+h/2=1 := by linarith
  simp only [rivalLaw,Measure.add_apply,Measure.smul_apply,
    smul_eq_mul,Measure.map_apply hlow MeasurableSet.univ,preimage_univ,
    measure_univ,Measure.dirac_apply_of_mem (mem_univ _),mul_one]
  rw [← ENNReal.ofReal_add hs ha,
    ← ENNReal.ofReal_add (add_nonneg hs ha) (by positivity),
    ← ENNReal.ofReal_add (by positivity : 0 ≤ s + a + h/2) (by positivity),ht]
  simp

def classCount {N : ℕ} (k : Fin 4) (omega : Fin N→RowRival) : ℕ :=
  ∑i,if (omega i).1=k then 1 else 0

def rowLowList {N : ℕ} (b : ℝ) (omega : Fin N→RowRival) : LocalList (N+1) :=
  Fin.cons (some b) (fun i=>if (omega i).1=0 then some (omega i).2 else none)

def rowResidual {N : ℕ} (c : ℕ) (j : Fin 2) (omega : Fin N→RowRival) : ℕ :=
  min (1+classCount 0 omega) (c-classCount 1 omega-classCount ⟨2+j.val,by omega⟩ omega)

theorem rowLowList_card {N : ℕ} (b : ℝ) (omega : Fin N→RowRival) :
    (Finset.univ.filter (fun i=>rowLowList b omega i≠none)).card=1+classCount 0 omega := by
  classical
  rw [Finset.card_eq_sum_ones,Finset.sum_filter]
  rw [Fin.sum_univ_succ]
  simp only [rowLowList,Fin.cons_zero,Fin.cons_succ,ne_eq,Option.some_ne_none,not_false_eq_true,
    if_true,add_comm 1]
  congr 1
  unfold classCount
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : (omega i).1=0 <;> simp [hi]

theorem rowResidual_le_card {N : ℕ} (c : ℕ) (j : Fin 2) (b : ℝ)
    (omega : Fin N→RowRival) :
    rowResidual c j omega≤(Finset.univ.filter (fun i=>rowLowList b omega i≠none)).card := by
  rw [rowLowList_card]
  exact min_le_left _ _

theorem rowResidual_le_capacity {N : ℕ} (c : ℕ) (j : Fin 2)
    (omega : Fin N→RowRival) : rowResidual c j omega≤c :=
  (min_le_right _ _).trans (Nat.sub_le _ _ |>.trans (Nat.sub_le _ _))

end FCAppendix.Affine.LowBody
