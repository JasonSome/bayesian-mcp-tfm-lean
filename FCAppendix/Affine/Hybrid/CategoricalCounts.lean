import FCAppendix.Affine.LowBody.ArrivalUnderflow
import FCAppendix.Probability.FiniteHoeffding

noncomputable section
namespace FCAppendix.Affine.Hybrid
open MeasureTheory ProbabilityTheory Set Filter Topology Classical
open scoped BigOperators
open Affine.LowBody

def categoryCount {N : ℕ} (k : Fin 4) (row : Fin N→Fin 4) : ℕ :=
  hitCount (fun t=>t=k) row

theorem categoryCount_cons {N : ℕ} (k t : Fin 4) (row : Fin N→Fin 4) :
    categoryCount k (Fin.cons t row)=(if t=k then 1 else 0)+categoryCount k row :=
  by
    unfold categoryCount hitCount
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero,Fin.cons_succ]
    by_cases hk : t=k <;> simp only [hk,↓reduceIte] <;>
      congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> split_ifs <;> rfl

lemma category_indicator_mean (C : FiniteLaw (Fin 4)) (k : Fin 4) :
    C.expect (fun t=>if t=k then (1:ℝ) else 0)=C.mass k := C.expect_singleton k

theorem categoryCount_deviation_le (C : FiniteLaw (Fin 4)) (N : ℕ)
    (k : Fin 4) {δ : ℝ} (hδ : 0≤δ) :
    (CommonList.iid C N).prob (fun row=>
      (N:ℝ)*δ≤|(categoryCount k row:ℝ)-(N:ℝ)*C.mass k|)≤
      2*Real.exp (-2*(N:ℝ)*δ^2) := by
  let X : Fin 4→ℝ:=fun t=>if t=k then 1 else 0
  have hX : ∀t,X t∈Icc (0:ℝ) 1:=fun t=>by dsimp only [X];split_ifs <;> norm_num
  have hs (row : Fin N→Fin 4) : ∑i,X (row i)=(categoryCount k row:ℝ) := by
    simp only [categoryCount,hitCount,X,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  have hU:=FiniteCramer.iid_upper_hoeffding C X hX N hδ
  have hD:=FiniteCramer.iid_lower_hoeffding C X hX N hδ
  have he (row : Fin N→Fin 4) :
      (N:ℝ)*δ≤|(categoryCount k row:ℝ)-(N:ℝ)*C.mass k| ↔
      (N:ℝ)*(C.expect X+δ)≤∑i,X (row i) ∨
      (∑i,X (row i))≤(N:ℝ)*(C.expect X-δ) := by
    rw [hs,show C.expect X=C.mass k from category_indicator_mean C k]
    rw [le_abs]
    constructor <;> rintro (h|h) <;> first | left; linarith | right; linarith
  have hh:=(CommonList.iid C N).prob_union_le
    (fun row=>(N:ℝ)*(C.expect X+δ)≤∑i,X (row i))
    (fun row=>(∑i,X (row i))≤(N:ℝ)*(C.expect X-δ))
  have hp : (CommonList.iid C N).prob (fun row=>
      (N:ℝ)*δ≤|(categoryCount k row:ℝ)-(N:ℝ)*C.mass k|)=
      (CommonList.iid C N).prob (fun row=>
      (N:ℝ)*(C.expect X+δ)≤∑i,X (row i) ∨
      (∑i,X (row i))≤(N:ℝ)*(C.expect X-δ)) := by
    unfold FiniteLaw.prob
    apply FiniteLaw.expect_congr
    intro row
    dsimp only
    simp only [he]
    split_ifs <;> rfl
  rw [hp]
  linarith

theorem all_categoryCounts_deviation_le (C : FiniteLaw (Fin 4)) (N : ℕ)
    {δ : ℝ} (hδ : 0≤δ) :
    (CommonList.iid C N).prob (fun row=>∃k : Fin 4,
      (N:ℝ)*δ≤|(categoryCount k row:ℝ)-(N:ℝ)*C.mass k|)≤
      8*Real.exp (-2*(N:ℝ)*δ^2) := by
  let E : Fin 4→(Fin N→Fin 4)→Prop:=fun k row=>
    (N:ℝ)*δ≤|(categoryCount k row:ℝ)-(N:ℝ)*C.mass k|
  have hp : (CommonList.iid C N).prob (fun row=>∃k : Fin 4,E k row)≤
      ∑k : Fin 4,(CommonList.iid C N).prob (E k) := by
    simp only [FiniteLaw.prob_eq_expect]
    rw [←FiniteLaw.expect_finset_sum]
    apply FiniteLaw.expect_mono
    intro row
    by_cases h : ∃k : Fin 4,E k row
    · rw [if_pos h]
      obtain ⟨k,hk⟩:=h
      have hh : (1:ℝ)≤∑j : Fin 4,if E j row then (1:ℝ) else 0:=by
        have hb:=Finset.single_le_sum (f:=fun j : Fin 4=>if E j row then (1:ℝ) else 0)
          (fun j _=>by split_ifs <;> norm_num) (Finset.mem_univ k)
        simpa only [if_pos hk] using hb
      exact hh
    · simp only [h,if_false]
      exact Finset.sum_nonneg (fun _ _=>by split_ifs <;> norm_num)
  have hh:=Finset.sum_le_sum (fun (k : Fin 4) (_ : k∈Finset.univ)=>
    categoryCount_deviation_le C N k hδ)
  apply hp.trans
  dsimp only [E]
  have hh' : (∑ k, (CommonList.iid C N).prob (E k))≤4*(2*Real.exp (-2*(N:ℝ)*δ^2)):=by
    simpa only [E,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat] using hh
  linarith

lemma forced_categoryCount_offset {r : ℕ} (C : FiniteLaw (Fin 4))
    (fixed : Fin r→Fin 4) (k : Fin 4) :
    |(categoryCount k fixed:ℝ)-(r:ℝ)*C.mass k|≤r := by
  have hm0 : 0≤C.mass k:=C.nonneg k
  have hm1 : C.mass k≤1:=by
    have hh:=C.prob_le_one (fun t=>t=k)
    simpa only [FiniteLaw.prob_eq_expect,FiniteLaw.expect_singleton] using hh
  have hc0 : (0:ℝ)≤categoryCount k fixed:=Nat.cast_nonneg _
  have hc1 : (categoryCount k fixed:ℝ)≤r:=by
    exact_mod_cast (show categoryCount k fixed≤r from by
      unfold categoryCount hitCount
      calc
        _≤∑_ : Fin r,1:=Finset.sum_le_sum (fun i _=>by split_ifs <;> omega)
        _=r:=by simp)
  rw [abs_le]
  constructor <;> nlinarith [show (0:ℝ)≤r from Nat.cast_nonneg r]

theorem forced_categoryCounts_deviation_le {r : ℕ} (C : FiniteLaw (Fin 4))
    (fixed : Fin r→Fin 4) (N : ℕ) {δ : ℝ} (hδ : 0≤δ) :
    (CommonList.iid C N).prob (fun row=>∃k : Fin 4,
      (N:ℝ)*δ+r≤|(categoryCount k fixed:ℝ)+(categoryCount k row:ℝ)-
        (N+r:ℕ)*C.mass k|)≤8*Real.exp (-2*(N:ℝ)*δ^2) := by
  apply le_trans ((CommonList.iid C N).prob_mono ?_)
    (all_categoryCounts_deviation_le C N hδ)
  rintro row ⟨k,hk⟩
  refine ⟨k,?_⟩
  have ht:=abs_add_le ((categoryCount k row:ℝ)-(N:ℝ)*C.mass k)
    ((categoryCount k fixed:ℝ)-(r:ℝ)*C.mass k)
  have ho:=forced_categoryCount_offset C fixed k
  have he : (categoryCount k row:ℝ)-(N:ℝ)*C.mass k+
      ((categoryCount k fixed:ℝ)-(r:ℝ)*C.mass k)=
      (categoryCount k fixed:ℝ)+(categoryCount k row:ℝ)-(N+r:ℕ)*C.mass k:=by
    push_cast
    ring
  rw [he] at ht
  linarith

theorem forced_fractional_count_exception_le {r : ℕ} (C : FiniteLaw (Fin 4))
    (fixed : Fin r→Fin 4) (N : ℕ) {δ : ℝ} (hδ : 0≤δ) (hroom : (r:ℝ)≤N*δ/2) :
    (CommonList.iid C N).prob (fun row=>∃k : Fin 4,
      (N+r:ℕ)*δ≤|(categoryCount k fixed:ℝ)+(categoryCount k row:ℝ)-
        (N+r:ℕ)*C.mass k|)≤8*Real.exp (-(N:ℝ)*δ^2/2) := by
  have hh:=forced_categoryCounts_deviation_le C fixed N (show 0≤δ/2 by positivity)
  have hm:=(CommonList.iid C N).prob_mono (E:=fun row=>∃k : Fin 4,
      (N+r:ℕ)*δ≤|(categoryCount k fixed:ℝ)+(categoryCount k row:ℝ)-
        (N+r:ℕ)*C.mass k|) (F:=fun row=>∃k : Fin 4,
      (N:ℝ)*(δ/2)+r≤|(categoryCount k fixed:ℝ)+(categoryCount k row:ℝ)-
        (N+r:ℕ)*C.mass k|) (by
    rintro row ⟨k,hk⟩
    refine ⟨k,?_⟩
    have hrδ : 0≤(r:ℝ)*δ:=mul_nonneg (Nat.cast_nonneg _) hδ
    push_cast at hk ⊢
    nlinarith)
  have he : -2*(N:ℝ)*(δ/2)^2=-(N:ℝ)*δ^2/2:=by ring
  rw [he] at hh
  exact hm.trans hh

end FCAppendix.Affine.Hybrid
