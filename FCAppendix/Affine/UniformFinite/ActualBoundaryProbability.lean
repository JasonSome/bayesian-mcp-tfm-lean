import FCAppendix.Affine.UniformFinite.FiniteExperiment
import FCAppendix.Affine.UniformFinite.AtomEventRates
import FCAppendix.Affine.UniformFinite.ActualAtomCrossing

noncomputable section
namespace FCAppendix.Affine.UniformFinite
open Set MeasureTheory ProbabilityTheory Filter Topology Classical
open scoped BigOperators

namespace ActualBoundary

lemma expect_comm {A B : Type*} [Fintype A] [Fintype B]
    (μ : FiniteLaw A) (ν : FiniteLaw B) (f : A → B → ℝ) :
    μ.expect (fun a => ν.expect (f a)) =
      ν.expect (fun b => μ.expect (fun a => f a b)) := by
  unfold FiniteLaw.expect
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  ring

def lowerCoin (i : Row) : FiniteLaw Bool :=
  IndependentCounts.bernoulli (Uniform05.t i) (Uniform05.t_pos i).le
    (Uniform05.t_lt_one i).le

def fairCoin : FiniteLaw Bool :=
  IndependentCounts.bernoulli (1/2) (by norm_num) (by norm_num)

lemma expect_lowerCoin (i : Row) (f : Bool → ℝ) :
    (lowerCoin i).expect f = (1-Uniform05.t i)*f false + Uniform05.t i*f true :=
  IndependentCounts.expect_bernoulli _ _ _ f

lemma expect_fairCoin (f : Bool → ℝ) :
    fairCoin.expect f = (1/2)*f false + (1/2)*f true := by
  simp only [fairCoin, IndependentCounts.expect_bernoulli,
    show (1:ℝ)-1/2=1/2 by norm_num]

def categoryOfCoins (lower route : Bool) : Fin 3 :=
  if lower then 0 else if route then 1 else 2

lemma category_expect_split (i : Row) (f : Fin 3 → ℝ) :
    (categoryLaw i).expect f =
      (lowerCoin i).expect (fun low => fairCoin.expect
        (fun route => f (categoryOfCoins low route))) := by
  rw [expect_lowerCoin, expect_fairCoin, expect_fairCoin]
  unfold FiniteLaw.expect categoryLaw
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ]
  norm_num [categoryOfCoins, show (2:Fin 3)≠0 by decide]
  ring

theorem categoryRow_expect_split (i : Row) (N : ℕ)
    (f : (Fin N → Fin 3) → ℝ) :
    (categoryRowLaw i N).expect f =
      (CommonList.iid (lowerCoin i) N).expect (fun low =>
        (CommonList.iid fairCoin N).expect (fun route =>
          f (fun j => categoryOfCoins (low j) (route j)))) := by
  induction N with
  | zero =>
    simp only [categoryRowLaw, CommonList.expect_iid_zero]
    congr 1
    funext j
    exact Fin.elim0 j
  | succ N ih =>
    change (CommonList.iid (categoryLaw i) (N+1)).expect f = _
    rw [CommonList.expect_iid_succ, category_expect_split]
    simp only [categoryRowLaw] at ih
    simp_rw [ih]
    rw [CommonList.expect_iid_succ]
    apply (lowerCoin i).expect_congr
    intro l
    rw [expect_comm fairCoin (CommonList.iid (lowerCoin i) N)]
    apply (CommonList.iid (lowerCoin i) N).expect_congr
    intro low
    rw [CommonList.expect_iid_succ]
    apply fairCoin.expect_congr
    intro r
    apply (CommonList.iid fairCoin N).expect_congr
    intro route
    congr 1
    funext j
    refine Fin.cases ?_ (fun j => ?_) j <;> rfl

def lowerCount {N : ℕ} (mask : Fin N → Bool) : ℕ :=
  ∑ j, if mask j then 1 else 0

def upperSlots {N : ℕ} (mask : Fin N → Bool) : ℕ :=
  ∑ j, if mask j then 0 else 1

def maskedHeads {N : ℕ} (mask route : Fin N → Bool) : ℕ :=
  ∑ j, if mask j then 0 else if route j then 1 else 0

lemma lowerCount_add_upperSlots {N : ℕ} (mask : Fin N → Bool) :
    lowerCount mask + upperSlots mask = N := by
  unfold lowerCount upperSlots
  rw [← Finset.sum_add_distrib]
  have he (j : Fin N) : (if mask j then 1 else 0) +
      (if mask j then 0 else 1) = (1:ℕ) := by cases mask j <;> rfl
  simp only [he, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, mul_one]

lemma upperSlots_cons {N : ℕ} (b : Bool) (mask : Fin N → Bool) :
    upperSlots (Fin.cons b mask) = (if b then 0 else 1) + upperSlots mask := by
  simp only [upperSlots, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]

lemma maskedHeads_cons {N : ℕ} (b r : Bool) (mask route : Fin N → Bool) :
    maskedHeads (Fin.cons b mask) (Fin.cons r route) =
      (if b then 0 else if r then 1 else 0) + maskedHeads mask route := by
  simp only [maskedHeads, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]

def binomialMean (N : ℕ) (p : ℝ) (hp0 : 0≤p) (hp1 : p≤1) (f : ℕ→ℝ) : ℝ :=
  (IndependentCounts.binomial N p hp0 hp1).expect (fun k=>f k.val)

lemma binomialMean_succ (N : ℕ) (p : ℝ) (hp0 : 0≤p) (hp1 : p≤1) (f : ℕ→ℝ) :
    binomialMean (N+1) p hp0 hp1 f =
      (1-p)*binomialMean N p hp0 hp1 f +
      p*binomialMean N p hp0 hp1 (fun k=>f (1+k)) := by
  unfold binomialMean
  rw [IndependentCounts.expect_binomial_succ]
  simp only [IndependentCounts.val_add_false, IndependentCounts.val_add_true]

theorem maskedHeads_expect_binomial (N : ℕ) (mask : Fin N → Bool) (f : ℕ → ℝ) :
    (CommonList.iid fairCoin N).expect (fun route => f (maskedHeads mask route)) =
      (IndependentCounts.binomial (upperSlots mask) (1/2)
        (by norm_num) (by norm_num)).expect (fun k => f k.val) := by
  change _=binomialMean _ _ _ _ f
  induction N generalizing f with
  | zero =>
    rw [CommonList.expect_iid_zero]
    simp [maskedHeads, upperSlots, binomialMean, IndependentCounts.binomial]
  | succ N ih =>
    rw [← Fin.cons_self_tail mask]
    rw [CommonList.expect_iid_succ, upperSlots_cons]
    cases hmask : mask 0
    · simp only [maskedHeads_cons, Bool.false_eq_true, ↓reduceIte]
      rw [expect_fairCoin]
      simp only [Bool.false_eq_true, ↓reduceIte, zero_add]
      rw [ih (Fin.tail mask) f, ih (Fin.tail mask) (fun n=>f (1+n))]
      rw [Nat.add_comm 1, binomialMean_succ]
      norm_num
    · simp only [maskedHeads_cons, ↓reduceIte, zero_add]
      rw [FiniteLaw.expect_const]
      exact ih (Fin.tail mask) f

lemma binomial_point_probability (N K : ℕ) (p : ℝ) (hp0 : 0≤ p) (hp1 : p≤1) :
    (IndependentCounts.binomial N p hp0 hp1).prob (fun k => k.val=K) =
      PiBinomial.pmf N p K := by
  by_cases hK : K< N+1
  · rw [FiniteLaw.prob_eq_expect]
    have he (k : Fin (N+1)) : k.val=K ↔ k=(⟨K,hK⟩:Fin (N+1)) :=
      ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩
    simp only [he, FiniteLaw.expect_singleton, PiBinomial.binomial_mass]
  · have hn (k : Fin (N+1)) : k.val ≠ K := by omega
    simp only [FiniteLaw.prob_eq_expect, hn, if_false, FiniteLaw.expect_zero,
      PiBinomial.pmf, Nat.choose_eq_zero_of_lt (show N< K by omega),
      Nat.cast_zero, zero_mul]

theorem maskedHeads_probability (N : ℕ) (mask : Fin N → Bool) (K : ℕ) :
    (CommonList.iid fairCoin N).prob (fun route => maskedHeads mask route=K) =
      PiBinomial.pmf (upperSlots mask) (1/2) K := by
  rw [FiniteLaw.prob_eq_expect,
    maskedHeads_expect_binomial N mask (fun k => if k=K then (1:ℝ) else 0),
    ← FiniteLaw.prob_eq_expect, binomial_point_probability]

theorem lowerCount_probability (i : Row) (N K : ℕ) :
    (CommonList.iid (lowerCoin i) N).prob (fun mask => lowerCount mask=K) =
      PiBinomial.pmf N (Uniform05.t i) K := by
  have hp : (lowerCoin i).prob (fun b => b=true)=Uniform05.t i := by
    rw [FiniteLaw.prob_eq_expect, expect_lowerCoin]
    norm_num
  have hc (mask : Fin N→Bool) : lowerCount mask=LowBody.hitCount (fun b=>b=true) mask := by
    unfold lowerCount LowBody.hitCount
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : mask j=true <;> simp [h]
  rw [FiniteLaw.prob_eq_expect]
  simp_rw [hc]
  have hh := LowBody.expect_hitCount_binomial (lowerCoin i) (fun b=>b=true) N
    (fun n=>if n=K then (1:ℝ) else 0)
  calc
    _ = (IndependentCounts.binomial N ((lowerCoin i).prob (fun b=>b=true))
        ((lowerCoin i).prob_nonneg _) ((lowerCoin i).prob_le_one _)).expect
          (fun k=>if k.val=K then (1:ℝ) else 0) := hh
    _ = PiBinomial.pmf N ((lowerCoin i).prob (fun b=>b=true)) K := by
      simpa only [FiniteLaw.prob_eq_expect] using
        (binomial_point_probability N K ((lowerCoin i).prob (fun b=>b=true))
          ((lowerCoin i).prob_nonneg _) ((lowerCoin i).prob_le_one _))
    _ = _ := by rw [hp]

def lowerKindCount {N : ℕ} (kind : Fin N → Fin 3) : ℕ :=
  LowBody.hitCount (fun k => k=0) kind

def upperZeroCount {N : ℕ} (kind : Fin N → Fin 3) : ℕ :=
  LowBody.hitCount (fun k => k=1) kind

def higherLowerCount {N : ℕ} (b : Fin N → ℝ) (u : ℝ) (kind : Fin N → Fin 3) : ℕ :=
  ∑ j, if kind j=0 ∧ u< b j then 1 else 0

def maskedHigherCount {N : ℕ} (b : Fin N → ℝ) (u : ℝ) (mask : Fin N → Bool) : ℕ :=
  ∑ j, if mask j=true ∧ u< b j then 1 else 0

lemma split_counts {N : ℕ} (b : Fin N → ℝ) (u : ℝ) (mask route : Fin N → Bool) :
    lowerKindCount (fun j => categoryOfCoins (mask j) (route j)) = lowerCount mask ∧
    upperZeroCount (fun j => categoryOfCoins (mask j) (route j)) = maskedHeads mask route ∧
    higherLowerCount b u (fun j => categoryOfCoins (mask j) (route j)) =
      maskedHigherCount b u mask := by
  constructor
  · unfold lowerKindCount LowBody.hitCount lowerCount
    apply Finset.sum_congr rfl
    intro j _
    cases hm : mask j <;> cases hr : route j <;> norm_num [categoryOfCoins, hm, hr]; decide
  constructor
  · unfold upperZeroCount LowBody.hitCount maskedHeads
    apply Finset.sum_congr rfl
    intro j _
    cases hm : mask j <;> cases hr : route j <;> norm_num [categoryOfCoins, hm, hr]; decide
  · unfold higherLowerCount maskedHigherCount
    apply Finset.sum_congr rfl
    intro j _
    cases hm : mask j <;> cases hr : route j <;> simp [categoryOfCoins, hm, hr]

lemma maskedHigherCount_le_lowerCount {N : ℕ}
    (b : Fin N → ℝ) (u : ℝ) (mask : Fin N → Bool) :
    maskedHigherCount b u mask ≤ lowerCount mask := by
  unfold maskedHigherCount lowerCount
  apply Finset.sum_le_sum
  intro j _
  by_cases hm : mask j=true
  · simp only [hm, true_and, if_true]
    split_ifs <;> omega
  · have hf : mask j=false := Bool.eq_false_of_not_eq_true hm
    simp only [hf, Bool.false_eq_true, false_and, if_false, le_refl]

def boundaryEvent {N : ℕ} (c L : ℕ) (b : Fin N → ℝ) (u : ℝ) :
    (Fin N → Fin 3) → Prop := fun kind =>
  lowerKindCount kind=L ∧ upperZeroCount kind=c-higherLowerCount b u kind-1

theorem literal_H_probability (i : Row) (N c L : ℕ) (hN : N=L+2*c)
    (b : Fin N → ℝ) (u : ℝ) :
    PiBinomial.pmf N (Uniform05.t i) L * PiBinomial.pmf (2*c) (1/2) (c-L-1) ≤
      (categoryRowLaw i N).prob (boundaryEvent c L b u) := by
  rw [FiniteLaw.prob_eq_expect, categoryRow_expect_split]
  have hpoint (mask : Fin N → Bool) :
      (if lowerCount mask=L then PiBinomial.pmf (2*c) (1/2) (c-L-1) else 0) ≤
        (CommonList.iid fairCoin N).expect (fun route =>
          if boundaryEvent c L b u (fun j => categoryOfCoins (mask j) (route j))
          then (1:ℝ) else 0) := by
    simp only [boundaryEvent, (split_counts b u mask _).1,
      (split_counts b u mask _).2.1, (split_counts b u mask _).2.2]
    by_cases hl : lowerCount mask=L
    · simp only [hl, true_and, if_true]
      rw [← FiniteLaw.prob_eq_expect, maskedHeads_probability]
      have hupp : upperSlots mask=2*c := by
        have hc := lowerCount_add_upperSlots mask
        omega
      rw [hupp]
      exact AtomEvents.fair_boundary_mass_lower c L (maskedHigherCount b u mask)
        (by simpa only [hl] using maskedHigherCount_le_lowerCount b u mask)
    · simp only [hl, false_and, if_false, FiniteLaw.expect_zero, le_refl]
  have hh := (CommonList.iid (lowerCoin i) N).expect_mono hpoint
  have hleft : (CommonList.iid (lowerCoin i) N).expect
      (fun mask => if lowerCount mask=L then PiBinomial.pmf (2*c) (1/2) (c-L-1) else 0) =
        PiBinomial.pmf N (Uniform05.t i) L * PiBinomial.pmf (2*c) (1/2) (c-L-1) := by
    calc
      _ = (CommonList.iid (lowerCoin i) N).expect
          (fun mask => (if lowerCount mask=L then (1:ℝ) else 0) *
            PiBinomial.pmf (2*c) (1/2) (c-L-1)) := by
        apply FiniteLaw.expect_congr
        intro mask
        split_ifs <;> simp
      _ = _ := by
        rw [FiniteLaw.expect_mul_const, ← FiniteLaw.prob_eq_expect,
          lowerCount_probability]
  rw [hleft] at hh
  exact hh

theorem source_H_probability (i : Row) (M : ℕ)
    (hM : 2*Uniform07.capacity M+2≤ M)
    (b : Fin (M-2) → ℝ) (u : ℝ) :
    AtomEvents.boundaryEvent (Uniform05.t i) M ≤
      (categoryRowLaw i (M-2)).prob
        (boundaryEvent (Uniform07.capacity M) (AtomEvents.otherLower M) b u) := by
  unfold AtomEvents.boundaryEvent
  exact literal_H_probability i (M-2) (Uniform07.capacity M) (AtomEvents.otherLower M)
    (by unfold AtomEvents.otherLower; omega) b u

lemma higherLowerCount_le {N : ℕ} (b : Fin N → ℝ) (u : ℝ)
    (kind : Fin N → Fin 3) : higherLowerCount b u kind ≤ lowerKindCount kind := by
  unfold higherLowerCount lowerKindCount LowBody.hitCount
  apply Finset.sum_le_sum
  intro j _
  by_cases hk : kind j=0
  · simp only [hk, true_and, if_true]
    split_ifs <;> omega
  · simp only [hk, false_and, if_false, le_refl]

lemma countRow_lowerCard {M : ℕ} (kind : Fin M → Fin 3) :
    (Source.countRowOfKind kind).lower.card = lowerKindCount kind := by
  classical
  simp only [Source.countRowOfKind, Finset.card_eq_sum_ones, Finset.sum_filter,
    lowerKindCount, LowBody.hitCount]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : kind j=0 <;> simp [h]

lemma countRow_upperZero {M : ℕ} (kind : Fin M → Fin 3) :
    (Source.countRowOfKind kind).upper0 = upperZeroCount kind := by
  classical
  simp only [Source.countRowOfKind, Finset.card_eq_sum_ones, Finset.sum_filter,
    upperZeroCount, LowBody.hitCount]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : kind j=1 <;> simp [h]

def pairKind {N : ℕ} (kind : Fin N → Fin 3) : Fin (N+2) → Fin 3 :=
  Fin.cons 0 (Fin.cons 0 kind)

def pairRow {N : ℕ} (kind : Fin N → Fin 3) : Source.CountRow (N+2) :=
  Source.countRowOfKind (pairKind kind)

def pairFullBids {N : ℕ} (b : Fin N → ℝ) (x y : ℝ) : Fin (N+2) → ℝ :=
  Fin.cons x (Fin.cons y b)

lemma pairRow_lowerCard {N : ℕ} (kind : Fin N → Fin 3) :
    (pairRow kind).lower.card = lowerKindCount kind+2 := by
  rw [pairRow, countRow_lowerCard]
  change LowBody.hitCount (fun k : Fin 3=>k=0) (Fin.cons 0 (Fin.cons 0 kind)) =
    LowBody.hitCount (fun k : Fin 3=>k=0) kind+2
  rw [LowBody.hitCount_cons, LowBody.hitCount_cons]
  norm_num
  omega

lemma pairRow_upperZero {N : ℕ} (kind : Fin N → Fin 3) :
    (pairRow kind).upper0 = upperZeroCount kind := by
  rw [pairRow, countRow_upperZero]
  change LowBody.hitCount (fun k : Fin 3=>k=1) (Fin.cons 0 (Fin.cons 0 kind)) =
    LowBody.hitCount (fun k : Fin 3=>k=1) kind
  rw [LowBody.hitCount_cons, LowBody.hitCount_cons]
  simp only [show (0:Fin 3)≠1 by decide, if_false, zero_add]

lemma pairRow_focal_mem {N : ℕ} (kind : Fin N → Fin 3) :
    (0:Fin (N+2)) ∈ (pairRow kind).lower := by
  simp [pairRow, Source.countRowOfKind, pairKind]

lemma pairRow_rival_mem {N : ℕ} (kind : Fin N → Fin 3) :
    (1:Fin (N+2)) ∈ (pairRow kind).lower := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  change (Fin.cons (0:Fin 3) (Fin.cons 0 kind) : Fin (N+2)→Fin 3) 1=0
  rfl

theorem boundary_residuals {N : ℕ} (L : ℕ)
    (hN : N=L+2*Uniform07.capacity (N+2))
    (hroom : L+1< Uniform07.capacity (N+2))
    (b : Fin N → ℝ) (u : ℝ) (kind : Fin N → Fin 3)
    (hkind : boundaryEvent (Uniform07.capacity (N+2)) L b u kind) :
    Source.residual (pairRow kind) 0 = higherLowerCount b u kind+1 ∧
    Source.residual (pairRow kind) 1 = 0 := by
  have hk := higherLowerCount_le b u kind
  have hlow := pairRow_lowerCard kind
  have hupper := pairRow_upperZero kind
  have hpartition := (pairRow kind).partition
  rcases hkind with ⟨hlower, hhead⟩
  rw [hlower] at hk hlow
  rw [hhead] at hupper
  have hleft : Uniform07.capacity (N+2)-(pairRow kind).upper0 =
      higherLowerCount b u kind+1 := by omega
  have hright : Uniform07.capacity (N+2) ≤ (pairRow kind).upper1 := by omega
  constructor
  · simp only [Source.residual, Source.upperCount, if_true, hleft]
    exact min_eq_right (by omega)
  · simp only [Source.residual, Source.upperCount]
    norm_num only [Fin.ext_iff, Fin.val_zero, Fin.val_one, Nat.one_ne_zero, if_false]
    rw [Nat.sub_eq_zero_of_le hright, Nat.min_zero]

theorem boundary_residual_positive {N : ℕ} (L : ℕ)
    (hN : N=L+2*Uniform07.capacity (N+2))
    (hroom : L+1< Uniform07.capacity (N+2))
    (b : Fin N → ℝ) (u : ℝ) (kind : Fin N → Fin 3)
    (hkind : boundaryEvent (Uniform07.capacity (N+2)) L b u kind) :
    0 < Source.residual (pairRow kind) 0 ∧ Source.residual (pairRow kind) 1=0 := by
  obtain ⟨hl, hr⟩ := boundary_residuals L hN hroom b u kind hkind
  exact ⟨by omega, hr⟩

lemma pairRestAbove_source_card {N : ℕ} (kind : Fin N→ Fin 3)
    (b : Fin N→ℝ) (u : ℝ) (hu : 0≤ u) (x y : ℝ) :
    (LowBody.pairRestAbove u (0:Fin (N+2)) (0:Fin (N+1)).succ
      (Source.lowerBids (pairRow kind) (pairFullBids b x y))).card =
        higherLowerCount b u kind := by
  unfold LowBody.pairRestAbove higherLowerCount
  rw [Finset.card_filter, Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp only [ne_eq, not_true_eq_false, false_and, if_false, zero_add,
    Fin.succ_ne_zero]
  simp only [not_false_eq_true, and_false, true_and, if_false, zero_add]
  apply Finset.sum_congr rfl
  intro k _
  have h1 : k.succ.succ≠(0:Fin (N+1)).succ :=
    fun he => Fin.succ_ne_zero k (Fin.succ_inj.mp he)
  have h1lit : k.succ.succ≠(1:Fin (N+2)) := by simpa using h1
  by_cases hk : kind k=0
  · simp [Source.lowerBids, pairRow, Source.countRowOfKind, pairKind,
      pairFullBids, h1lit, hk]
  · simp [Source.lowerBids, pairRow, Source.countRowOfKind, pairKind,
      h1lit, hk, not_lt_of_ge hu]

theorem boundary_pair_count {N : ℕ} (L : ℕ)
    (hN : N=L+2*Uniform07.capacity (N+2))
    (hroom : L+1< Uniform07.capacity (N+2))
    (b : Fin N→ℝ) (u : ℝ) (hu : 0≤ u) (kind : Fin N→ Fin 3)
    (hkind : boundaryEvent (Uniform07.capacity (N+2)) L b u kind) (x y : ℝ) :
    (LowBody.pairRestAbove u (0:Fin (N+2)) (0:Fin (N+1)).succ
      (Source.lowerBids (pairRow kind) (pairFullBids b x y))).card+1 =
        Source.residual (pairRow kind) 0 := by
  rw [pairRestAbove_source_card kind b u hu x y,
    (boundary_residuals L hN hroom b u kind hkind).1]

end ActualBoundary
end FCAppendix.Affine.UniformFinite
