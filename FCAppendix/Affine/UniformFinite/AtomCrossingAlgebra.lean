import FCAppendix.Affine.LowBody.PureCopyMonotonicity
import FCAppendix.Affine.LowBody.FirstCopyPair
import FCAppendix.Affine.LowBody.PureFiniteCrossing
import FCAppendix.Affine.LowBody.ClusterIteration
import FCAppendix.Affine.UniformFinite.AtomEventRates

noncomputable section

namespace FCAppendix.Affine.UniformFinite

open MeasureTheory Set Filter Topology
open scoped BigOperators

namespace CopyAlgebra

def payoff (η v b : ℝ) (n : Fin 3) : ℝ :=
  if n=2 then v-(1+η)*b else if n=1 then v-b else 0

lemma payoff_le_surplus (η v b : ℝ) (hη : 0≤η) (hb0 : 0≤ b) (hbv : b≤ v)
    (n : Fin 3) : payoff η v b n≤ v-b := by
  fin_cases n <;> simp [payoff,Fin.ext_iff] <;> nlinarith

lemma payoff_nonpos_of_overbid (η v b : ℝ) (hη : 0≤η)
    (hv0 : 0≤ v) (hvb : v< b) (n : Fin 3) : payoff η v b n≤0 := by
  have hb0 : 0≤ b := hv0.trans hvb.le
  fin_cases n <;> simp [payoff,Fin.ext_iff] <;> nlinarith

lemma payoff_nonneg_below_fraction (η v b χ : ℝ) (hη : 0≤η)
    (hv : 0≤ v) (hb : 0≤ b) (hbχ : b≤χ*v) (hχ : (1+η)*χ≤1)
    (n : Fin 3) : 0≤ payoff η v b n := by
  have hη1 : 0≤1+η := by linarith
  have hcost : (1+η)*b≤ v := by
    have h1 := mul_le_mul_of_nonneg_left hbχ hη1
    have h2 := mul_le_mul_of_nonneg_right hχ hv
    nlinarith
  have hbv : b≤ v := by nlinarith
  fin_cases n <;> simp [payoff,Fin.ext_iff] <;> linarith

theorem comparison_expectation_lower {Ω : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) (η v b χ : ℝ) (hη : 0≤η) (hv : 0≤ v)
    (hb : 0≤ b) (hbχ : b≤χ*v) (hχ : (1+η)*χ≤1)
    (copies : Ω→ Fin 3) (E : Ω→ Prop) (hE : ∀ω,E ω→ copies ω=1) :
    (1-χ)*v*μ.prob E≤μ.expect (fun ω => payoff η v b (copies ω)) := by
  classical
  have hh := μ.expect_mono (f:=fun ω => (1-χ)*v*(if E ω then 1 else 0))
    (g:=fun ω => payoff η v b (copies ω)) (by
      intro ω
      by_cases hω : E ω
      · rw [if_pos hω,hE ω hω]
        simp only [mul_one,payoff]
        norm_num [Fin.ext_iff]
        nlinarith
      · rw [if_neg hω,mul_zero]
        exact payoff_nonneg_below_fraction η v b χ hη hv hb hbχ hχ (copies ω))
  simpa only [FiniteLaw.expect_const_mul,← FiniteLaw.prob_eq_expect] using hh

lemma affine_noise_range (lo hi v ε q z : ℝ)
    (hlo : 0≤ lo) (hwidth : lo≤ hi) (hhi : hi≤ v)
    (hε : 0≤ε) (hz : z∈Icc (0:ℝ) 1) :
    lo+(hi-lo)*(1-ε)*q ≤ lo+(hi-lo)*((1-ε)*q+ε*z) ∧
    lo+(hi-lo)*((1-ε)*q+ε*z) ≤ lo+(hi-lo)*(1-ε)*q+ε*v := by
  have hw0 : 0≤ hi-lo := sub_nonneg.mpr hwidth
  have hwv : hi-lo≤ v := by linarith
  have hzprod : 0≤(hi-lo)*ε*z := mul_nonneg (mul_nonneg hw0 hε) hz.1
  have hzle := mul_le_mul_of_nonneg_left hz.2 (mul_nonneg hw0 hε)
  have hwle := mul_le_mul_of_nonneg_left hwv hε
  constructor <;> nlinarith

theorem noisy_physical_surplus (χ L ε v b bmin incumbent : ℝ)
    (hχ : χ<1) (hL0 : 0≤ L) (hL1 : L≤1)
    (hε0 : 0≤ε) (hε : ε≤(1-χ)*L/4)
    (hv : 0≤ v) (hbv : b≤ v) (hbrange : b≤ bmin+ε*v)
    (hcomparison : (1-χ-ε)*v*L≤ incumbent)
    (hupper : incumbent≤ v-bmin) :
    (1-χ)*b*L/2≤ v-b := by
  have hχ0 : 0≤1-χ := by linarith
  have hLplus : ε*(L+1)≤(1-χ)*L/2 := by
    nlinarith [mul_nonneg hε0 (sub_nonneg.mpr hL1)]
  have hscaled := mul_le_mul_of_nonneg_right hLplus hv
  have hbid := mul_le_mul_of_nonneg_right hbv (div_nonneg (mul_nonneg hχ0 hL0) (by norm_num : (0:ℝ)≤2))
  nlinarith

end CopyAlgebra

namespace PureAtoms

open LowBody

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem unserved_bid_le_scaled_duplicate (T : PureTemplate ι) (κ : ℝ)
    (b : ι→ℝ) (i : ι)
    (hi : i∈(T.selection κ b).1∩(T.selection κ b).2)
    (j : ι) (hj : j∈T.support \ ((T.selection κ b).1∪(T.selection κ b).2)) :
    b j≤κ*b i := by
  let P := T.selection κ b
  let r : ι→ℝ := fun k => if k∈P.2 then κ*b k else b k
  have hf := T.selection_feasible κ b
  have hiS : i∈P.1 := (Finset.mem_inter.mp hi).1
  have hiT : i∈P.2 := (Finset.mem_inter.mp hi).2
  have hjSup : j∈T.support := (Finset.mem_sdiff.mp hj).1
  have hjNot : j∉P.1∪P.2 := (Finset.mem_sdiff.mp hj).2
  have hjS : j∉P.1 := fun h => hjNot (Finset.mem_union_left _ h)
  have hjT : j∉P.2 := fun h => hjNot (Finset.mem_union_right _ h)
  have hjErase : j∉P.1.erase i := fun h => hjS (Finset.mem_of_mem_erase h)
  have hcard : (insert j (P.1.erase i)).card≤ T.residual₀ := by
    rw [Finset.card_insert_of_notMem hjErase,Finset.card_erase_of_mem hiS]
    have hpos : 0< P.1.card := Finset.card_pos.mpr ⟨i,hiS⟩
    have hf0 : P.1.card≤ T.residual₀ := hf.1
    omega
  have hsub : insert j (P.1.erase i)⊆T.support := by
    intro k hk
    rcases Finset.mem_insert.mp hk with hkj | hkErase
    · exact hkj ▸ hjSup
    · exact hf.2.1 (Finset.mem_of_mem_erase hkErase)
  have hnash := (T.selection_nash κ b).1 (insert j (P.1.erase i)) hcard hsub
  change (∑k∈insert j (P.1.erase i),r k)≤∑k∈P.1,r k at hnash
  rw [Finset.sum_insert hjErase] at hnash
  have hs := Finset.sum_erase_add P.1 r hiS
  have hri : r i=κ*b i := by simp [r,hiT]
  have hrj : r j=b j := by simp [r,hjT]
  rw [hri] at hs
  rw [hrj] at hnash
  linarith

theorem unserved_count_of_duplicate (T : PureTemplate ι) (κ : ℝ)
    (b : ι→ℝ) (i : ι)
    (hi : i∈(T.selection κ b).1∩(T.selection κ b).2) :
    T.support.card+1 ≤
      (T.support \ ((T.selection κ b).1∪(T.selection κ b).2)).card+
        T.residual₀+T.residual₁ := by
  let P := T.selection κ b
  have hf := T.selection_feasible κ b
  have hsub : P.1∪P.2⊆T.support := Finset.union_subset hf.2.1 hf.2.2.2
  have hcard := Finset.card_le_card hsub
  have hinter : 1≤(P.1∩P.2).card := Finset.card_pos.mpr ⟨i,hi⟩
  have hidentity := Finset.card_union_add_card_inter P.1 P.2
  have hcard₀ := hf.1
  have hcard₁ := hf.2.2.1
  change P.1.card ≤ T.residual₀ at hcard₀
  change P.2.card ≤ T.residual₁ at hcard₁
  change T.support.card+1 ≤ (T.support \ (P.1∪P.2)).card+T.residual₀+T.residual₁
  rw [Finset.card_sdiff_of_subset hsub]
  omega

theorem small_bid_count_of_duplicate (T : PureTemplate ι) (κ : ℝ)
    (b : ι→ℝ) (i : ι)
    (hi : i∈(T.selection κ b).1∩(T.selection κ b).2) :
    T.support.card+1 ≤
      (T.support.filter (fun j => j≠i ∧ b j≤κ*b i)).card+
        T.residual₀+T.residual₁ := by
  have hsub : T.support \ ((T.selection κ b).1∪(T.selection κ b).2) ⊆
      T.support.filter (fun j => j≠i ∧ b j≤κ*b i) := by
    intro j hj
    apply Finset.mem_filter.mpr
    refine ⟨(Finset.mem_sdiff.mp hj).1,?_,unserved_bid_le_scaled_duplicate T κ b i hi j hj⟩
    intro hji
    subst j
    exact (Finset.mem_sdiff.mp hj).2
      (Finset.mem_union_left _ (Finset.mem_inter.mp hi).1)
  have hcard := Finset.card_le_card hsub
  have hcount := unserved_count_of_duplicate T κ b i hi
  omega

theorem duplicate_acquisition_small_count {n : ℕ}
    (T : PureTemplate (Fin n)) {κ : ℝ} (hκ : 0<κ)
    (b : Fin n→ℝ) (hb : ∀j,0≤ b j)
    (hz : ∀j,j∉T.support→ b j=0) (i : Fin n) (hi : i∈T.support)
    (hbi : 0< b i) (y : ℝ) (hy : b i< y)
    (hnot : focalCopy (T.selection κ b) i≠2)
    (hdup : focalCopy (T.selection κ (Function.update b i y)) i=2) :
    ∃j : Fin n,j∈T.support ∧ j≠i ∧
      (b j∈Icc (b i) y ∨ b j∈Icc (κ*b i) (κ*y)) ∧
      T.support.card≤
        ((T.support.filter (fun k => k≠i ∧ b k≤κ*y)).erase j).card+
          T.residual₀+T.residual₁ := by
  obtain ⟨_,_,j,hj,hji,hcluster⟩ := T.duplicate_acquisition_interval hκ b hb hz i hi hbi y hy hnot hdup
  have himem : i∈(T.selection κ (Function.update b i y)).1∩
      (T.selection κ (Function.update b i y)).2 :=
    (LowBody.focalCopy_eq_two_iff _ _).mp hdup
  have hcount := small_bid_count_of_duplicate T κ (Function.update b i y) i himem
  have heq : T.support.filter (fun k => k≠i ∧
      Function.update b i y k≤κ*Function.update b i y i) =
      T.support.filter (fun k => k≠i ∧ b k≤κ*y) := by
    ext k
    by_cases hki : k=i
    · subst k; simp
    · simp [hki]
  rw [heq] at hcount
  let A := T.support.filter (fun k => k≠i ∧ b k≤κ*y)
  have hdel : A.card≤(A.erase j).card+1 := by
    by_cases hjA : j∈A
    · rw [Finset.card_erase_of_mem hjA]
      have hp : 0< A.card := Finset.card_pos.mpr ⟨j,hjA⟩
      omega
    · rw [Finset.erase_eq_of_notMem hjA]
      omega
  refine ⟨j,hj,hji,hcluster,?_⟩
  change T.support.card≤(A.erase j).card+T.residual₀+T.residual₁
  change T.support.card+1≤ A.card+T.residual₀+T.residual₁ at hcount
  omega

theorem pure_raising_gain_lower (T : PureTemplate ι) {κ : ℝ} (hκ : 1/2≤κ)
    (b : ι→ℝ) (i : ι) (v y : ℝ) (hbv : b i≤ v) (hy : b i< y) :
    -(if focalCopy (T.selection κ b) i≠2 ∧
        focalCopy (T.selection κ (Function.update b i y)) i=2
      then (2*κ-1)*b i else 0) - 2*κ*(y-b i) ≤
      purePayoff κ v (Function.update b i y) (T.selection κ (Function.update b i y)) i-
        purePayoff κ v b (T.selection κ b) i := by
  let Q := T.selection κ (Function.update b i y)
  have hm := T.focalCopy_selection_mono (by linarith : 0<κ) b i y hy
  have hcopyloss := purePayoff_loss_le_duplicate (κ := κ) b i hbv (T.selection κ b) Q hm
  have hprice : purePayoff κ v b Q i-
      purePayoff κ v (Function.update b i y) Q i≤2*κ*(y-b i) := by
    unfold purePayoff
    rw [Function.update_self]
    generalize focalCopy Q i=q
    fin_cases q <;> simp [Fin.ext_iff] <;> nlinarith
  change -(if focalCopy (T.selection κ b) i≠2 ∧ focalCopy Q i=2
      then (2*κ-1)*b i else 0)-2*κ*(y-b i)≤
    purePayoff κ v (Function.update b i y) Q i-purePayoff κ v b (T.selection κ b) i
  linarith

theorem zero_bid_right_domination (T : PureTemplate ι) {κ : ℝ}
    (hκ : 1/2≤κ) (b : ι→ℝ) (i : ι) (hbi : b i=0)
    (v x : ℝ) (hv : 0≤ v) (hx : 0< x) :
    purePayoff κ v b (T.selection κ b) i ≤
      purePayoff κ v (Function.update b i x)
        (T.selection κ (Function.update b i x)) i + 2*κ*x := by
  have hkpos : 0<κ := by linarith
  have hcopy := T.focalCopy_selection_mono hkpos b i x (by simpa only [hbi] using hx)
  unfold purePayoff
  rw [hbi,Function.update_self]
  generalize focalCopy (T.selection κ b) i=p at *
  generalize focalCopy (T.selection κ (Function.update b i x)) i=q at *
  fin_cases p <;> fin_cases q <;> simp_all [Fin.ext_iff] <;> nlinarith

end PureAtoms

end FCAppendix.Affine.UniformFinite
