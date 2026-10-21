import FCAppendix.Existence.Potential
import FCAppendix.Game.LocalInformation
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Topology.Constructions.SumProd

noncomputable section
namespace FCAppendix.Existence.PayOnceBounded
open Set Filter Topology MeasureTheory
open scoped BigOperators

section FiniteSupport
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def onSupport (n c : ℕ) (S : Finset ι) (b : ι → ℝ) (i : ι) : ℝ :=
  if hi : i ∈ S then
    CommonList.kernelMarginal (ι := ↥S) n c (fun j => b j.1) ⟨i, hi⟩
  else 0

omit [Fintype ι] in
@[simp] theorem onSupport_outside (n c : ℕ) (S : Finset ι) (b : ι → ℝ)
    (i : ι) (hi : i ∉ S) : onSupport n c S b i = 0 := by
  simp [onSupport, hi]

omit [Fintype ι] in
@[simp] theorem onSupport_inside (n c : ℕ) (S : Finset ι) (b : ι → ℝ)
    (i : S) : onSupport n c S b i.1 =
      CommonList.kernelMarginal (ι := ↥S) n c (fun j => b j.1) i := by
  simp [onSupport, i.2]

theorem onSupport_spec (n c : ℕ) (hn : 2 ≤ n) (S : Finset ι) (b : ι → ℝ)
    (hb : ∀ i ∈ S, 0 < b i) :
    (∀ i, 0 ≤ onSupport n c S b i) ∧
    (∀ i, onSupport n c S b i ≤ 1) ∧
    (∑ i, onSupport n c S b i = (min c S.card : ℕ)) := by
  have h := CommonList.kernelMarginal_spec n hn c (fun i : S => b i.1)
    (fun i => hb i.1 i.2)
  refine ⟨?_, ?_, ?_⟩
  · intro i
    by_cases hi : i ∈ S
    · simpa [onSupport, hi] using h.1 ⟨i, hi⟩
    · simp [onSupport, hi]
  · intro i
    by_cases hi : i ∈ S
    · simpa [onSupport, hi] using h.2.1 ⟨i, hi⟩
    · simp [onSupport, hi]
  · calc
      (∑ i, onSupport n c S b i) =
          ∑ i : S, CommonList.kernelMarginal n c (fun j : S => b j.1) i := by
            calc
              _ = ∑ i ∈ S, onSupport n c S b i :=
                (Finset.sum_subset (Finset.subset_univ S)
                  (fun i _ hi => onSupport_outside n c S b i hi)).symm
              _ = ∑ i : S, onSupport n c S b i := (Finset.sum_attach S _).symm
              _ = _ := by simp only [onSupport_inside]
      _ = (min c S.card : ℕ) := by simpa using h.2.2.1

omit [DecidableEq ι] in

theorem kernel_equiv {κ : Type*} [Fintype κ]
    (e : ι ≃ κ) (n c : ℕ) (hn : 2 ≤ n) (b : κ → ℝ) (hb : ∀ i, 0 < b i) :
    CommonList.kernelMarginal n c (b ∘ e) =
      CommonList.kernelMarginal n c b ∘ e := by
  apply (CommonList.eq_kernelMarginal n hn c (b ∘ e) (fun i => hb (e i)) _ ?_).symm
  obtain ⟨hp0, hp1, hsum, L, hL, hthreshold⟩ :=
    CommonList.kernelMarginal_spec n hn c b hb
  refine ⟨fun i => hp0 (e i), fun i => hp1 (e i), ?_, L, hL, ?_, ?_, ?_⟩
  · change (∑ i, CommonList.kernelMarginal n c b (e i)) = _
    rw [Equiv.sum_comp e]
    simpa [Fintype.card_congr e] using hsum
  · intro i hi
    exact hthreshold.1 (e i) hi
  · intro i hi
    exact hthreshold.2.1 (e i) hi
  · intro i hi0 hi1
    exact hthreshold.2.2 (e i) hi0 hi1

omit [DecidableEq ι] in

theorem kernel_pos_of_max (n c : ℕ) (hn : 2 ≤ n) (hc : 1 ≤ c)
    (b : ι → ℝ) (hb : ∀ i, 0 < b i) (i : ι) (hmax : ∀ j, b j ≤ b i) :
    0 < CommonList.kernelMarginal n c b i := by
  let p := CommonList.kernelMarginal n c b
  obtain ⟨hp0, hp1, hsum, L, hL, ht⟩ := CommonList.kernelMarginal_spec n hn c b hb
  have hcard : 1 ≤ Fintype.card ι := Fintype.card_pos_iff.mpr ⟨i⟩
  have hsumpos : 0 < ∑ j, p j := by
    rw [hsum]
    exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one (le_min hc hcard)
  obtain ⟨j, hj⟩ : ∃ j, 0 < p j := by
    by_contra hnone
    push Not at hnone
    have hnonpos : (∑ j, p j) ≤ 0 := Finset.sum_nonpos (fun j _ => hnone j)
    linarith
  by_contra hi
  have hpi : p i = 0 := le_antisymm (le_of_not_gt hi) (hp0 i)
  have his : PayOnce.ScalarThreshold n (b i) L (p i) :=
    ⟨hp0 i, hp1 i, ht.1 i, ht.2.1 i, ht.2.2 i⟩
  have hjs : PayOnce.ScalarThreshold n (b j) L (p j) :=
    ⟨hp0 j, hp1 j, ht.1 j, ht.2.1 j, ht.2.2 j⟩
  have hiL := PayOnce.scalar_receipt_le_of_lt_one n (b i) L (p i) his (by simp [hpi])
  have hjL := PayOnce.scalar_price_le_of_pos n (b j) L (p j) hjs hj
  have hH0 : PayOnce.H n 0 = 1 := by
    simp [PayOnce.H, Nat.ne_of_gt (show 0 < n by omega)]
  have hHj := PayOnce.H_strict n hn 0 (p j) hj (hp1 j)
  rw [hpi, hH0, mul_one] at hiL
  rw [hH0] at hHj
  have hrec : b j * PayOnce.H n (p j) < b i :=
    (mul_lt_of_lt_one_right (hb j) hHj).trans_le (hmax j)
  linarith

omit [Fintype ι] in

theorem continuousAt_onSupport (n c : ℕ) (hn : 2 ≤ n) (S : Finset ι)
    (b : ι → ℝ) (hb : ∀ i ∈ S, 0 < b i) :
    ContinuousAt (onSupport n c S) b := by
  rw [continuousAt_pi]
  intro i
  by_cases hi : i ∈ S
  · have hc := (CommonList.continuousAt_kernelMarginal n hn c
      (fun j : S => b j.1) (fun j => hb j.1 j.2)).comp
      (continuous_pi (fun j : S => continuous_apply j.1)).continuousAt
    convert (continuous_apply (⟨i, hi⟩ : S)).continuousAt.comp hc using 1
    funext y
    simp only [onSupport,dif_pos hi,Function.comp_apply]
  · simpa [onSupport, hi] using (continuousAt_const : ContinuousAt (fun _ : ι → ℝ => (0 : ℝ)) b)
end FiniteSupport

section FloorCarrier
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local instance : TopologicalSpace (Finset ι) := ⊥
local instance : DiscreteTopology (Finset ι) := ⟨rfl⟩

abbrev FloorAction (ε W : ℝ) := Unit ⊕ Icc ε W

def present {ε W : ℝ} : FloorAction ε W → Bool
  | .inl _ => false
  | .inr _ => true

def bid {ε W : ℝ} : FloorAction ε W → ℝ
  | .inl _ => 0
  | .inr b => b.1

theorem continuous_present {ε W : ℝ} : Continuous (@present ε W) :=
  continuous_sum_dom.mpr ⟨continuous_const, continuous_const⟩

theorem continuous_bid {ε W : ℝ} : Continuous (@bid ε W) :=
  continuous_sum_dom.mpr ⟨continuous_const, continuous_subtype_val⟩

def activeSet {ε W : ℝ} (x : ι → FloorAction ε W) : Finset ι :=
  Finset.univ.filter (fun i => present (x i))

omit [DecidableEq ι] in
@[simp] theorem mem_activeSet {ε W : ℝ} (x : ι → FloorAction ε W) (i : ι) :
    i ∈ activeSet x ↔ present (x i) = true := by simp [activeSet]

omit [DecidableEq ι] in
theorem continuous_activeSet {ε W : ℝ} :
    Continuous (activeSet : (ι → FloorAction ε W) → Finset ι) := by
  let f : (ι → Bool) → Finset ι := fun p => Finset.univ.filter (fun i => p i)
  exact (continuous_of_discreteTopology (f := f)).comp
    (continuous_pi fun i => continuous_present.comp (continuous_apply i))

theorem bid_pos_of_present {ε W : ℝ} (hε : 0 < ε) (x : FloorAction ε W)
    (hx : present x = true) : 0 < bid x := by
  rcases x with _ | b
  · simp [present] at hx
  · exact hε.trans_le b.2.1

def marginal {ε W : ℝ} (n c : ℕ) (x : ι → FloorAction ε W) : ι → ℝ :=
  onSupport n c (activeSet x) (fun i => bid (x i))

theorem marginal_spec {ε W : ℝ} (n c : ℕ) (hn : 2 ≤ n) (hε : 0 < ε)
    (x : ι → FloorAction ε W) :
    (∀ i, 0 ≤ marginal n c x i) ∧
    (∀ i, marginal n c x i ≤ 1) ∧
    (∑ i, marginal n c x i = (min c (activeSet x).card : ℕ)) := by
  apply onSupport_spec n c hn
  intro i hi
  exact bid_pos_of_present hε (x i) (mem_activeSet x i |>.mp hi)

theorem continuous_marginal {ε W : ℝ} (n c : ℕ) (hn : 2 ≤ n) (hε : 0 < ε) :
    Continuous (marginal n c : (ι → FloorAction ε W) → ι → ℝ) := by
  rw [continuous_iff_continuousAt]
  intro x
  have hpat : ∀ᶠ y in 𝓝 x, activeSet y = activeSet x :=
    continuous_activeSet.continuousAt.eventually
      ((isOpen_discrete {activeSet x}).mem_nhds (by simp))
  have hpos : ∀ i ∈ activeSet x, 0 < bid (x i) := fun i hi =>
    bid_pos_of_present hε (x i) ((mem_activeSet x i).mp hi)
  have hcont := (continuousAt_onSupport n c hn (activeSet x)
    (fun i => bid (x i)) hpos).comp
    (continuous_pi (fun i => continuous_bid.comp (continuous_apply i))).continuousAt
  apply hcont.congr_of_eventuallyEq
  filter_upwards [hpat] with y hy
  simp only [marginal, hy]
  rfl

theorem marginal_mono_own {ε W : ℝ} (n c : ℕ) (hn : 2 ≤ n) (hε : 0 < ε)
    (x : ι → FloorAction ε W) (i : ι) (b b' : Icc ε W) (hbb' : b.1 ≤ b'.1) :
    marginal n c (Function.update x i (.inr b)) i ≤
      marginal n c (Function.update x i (.inr b')) i := by
  let S := insert i (activeSet x)
  have hp : ∀ t : Icc ε W,
      activeSet (Function.update x i (.inr t)) = S := by
    intro t
    ext j
    by_cases hj : j = i
    · subst j; simp [activeSet, present, S]
    · simp [activeSet, present, S, hj]
  have hi : i ∈ S := Finset.mem_insert_self _ _
  simp only [marginal]
  rw [hp b,hp b']
  simp only [onSupport,dif_pos hi]
  refine CommonList.kernelMarginal_mono_own n hn c
    (fun j : S => bid (Function.update x i (.inr b) j.1))
    (fun j : S => bid (Function.update x i (.inr b') j.1)) ?_ ?_ ⟨i,hi⟩ ?_ ?_
  · intro j
    by_cases hj : j.1 = i
    · simp [hj, bid]; exact hε.trans_le b.2.1
    · have hjS : j.1 ∈ activeSet x := (Finset.mem_insert.mp j.2).resolve_left hj
      simpa [Function.update_of_ne hj] using
        bid_pos_of_present hε (x j.1) ((mem_activeSet x j.1).mp hjS)
  · intro j
    by_cases hj : j.1 = i
    · simp [hj, bid]; exact hε.trans_le b'.2.1
    · have hjS : j.1 ∈ activeSet x := (Finset.mem_insert.mp j.2).resolve_left hj
      simpa [Function.update_of_ne hj] using
        bid_pos_of_present hε (x j.1) ((mem_activeSet x j.1).mp hjS)
  · intro j hj
    have hji : j.1 ≠ i := by intro he; apply hj; exact Subtype.ext he
    simp [Function.update_of_ne hji]
  · simpa [bid] using hbb'

theorem marginal_saturates {ε W : ℝ} (n c : ℕ) (hn : 2 ≤ n) (hc : 1 ≤ c)
    (hε : 0 < ε) (x : ι → FloorAction ε W) (i : ι)
    (hi : present (x i) = true)
    (hdom : ∀ j, j ≠ i → present (x j) = true → bid (x j) < bid (x i) / n) :
    marginal n c x i = 1 := by
  have hmem : i ∈ activeSet x := (mem_activeSet x i).mpr hi
  simp only [marginal, onSupport, dif_pos hmem]
  apply CommonList.kernelMarginal_saturates n hn c hc
  · intro j; exact bid_pos_of_present hε _ ((mem_activeSet x j.1).mp j.2)
  · intro j hj
    apply hdom j.1
    · intro he; apply hj; exact Subtype.ext he
    · exact (mem_activeSet x j.1).mp j.2

def success {ε W : ℝ} (n c : ℕ) (x : ι → FloorAction ε W) (i : ι) : ℝ :=
  PayOnce.success n (marginal n c x i)

theorem success_bounds {ε W : ℝ} (n c : ℕ) (hn : 2 ≤ n) (hε : 0 < ε)
    (x : ι → FloorAction ε W) (i : ι) : 0 ≤ success n c x i ∧ success n c x i ≤ 1 := by
  have hp := marginal_spec n c hn hε x
  refine ⟨?_, PayOnce.success_le_one n _ (hp.2.1 i)⟩
  rw [success, ← PayOnce.H_mul n (by omega)]
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hp.1 i))
    (PayOnce.H_nonneg n _ (hp.2.1 i))

theorem success_mono_scalar (n : ℕ) {p q : ℝ} (_hp : 0 ≤ p) (hpq : p ≤ q)
    (hq : q ≤ 1) : PayOnce.success n p ≤ PayOnce.success n q := by
  have hh := pow_le_pow_left₀ (sub_nonneg.mpr hq) (show 1 - q ≤ 1 - p by linarith) n
  simpa [PayOnce.success] using sub_le_sub_left hh 1

theorem success_sum_le (n m c : ℕ) (hm : 0 < m)
    (p : Fin m → ℝ) (_hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (hsum : ∑ i, p i = (c : ℝ)) :
    ∑ i, PayOnce.success n (p i) ≤ m * PayOnce.success n ((c : ℝ) / m) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  let w : Fin m → ℝ := fun _ => 1 / m
  have hw0 : ∀ i ∈ (Finset.univ : Finset (Fin m)), 0 ≤ w i := by
    intro i _; dsimp [w]; positivity
  have hws : ∑ i : Fin m, w i = 1 := by simp [w, ne_of_gt hmR]
  have hx : ∀ i ∈ (Finset.univ : Finset (Fin m)), 1 - p i ∈ Ici (0 : ℝ) := by
    intro i _; exact sub_nonneg.mpr (hp1 i)
  have hj := (convexOn_pow n).map_sum_le hw0 hws hx
  simp only [smul_eq_mul] at hj
  have hmexpr : (∑ i : Fin m, w i * (1 - p i)) = 1 - (c : ℝ) / m := by
    simp only [w, mul_sub, mul_one, Finset.sum_sub_distrib]
    rw [← Finset.mul_sum, hsum]
    simp [ne_of_gt hmR, div_eq_mul_inv,mul_comm]
  rw [hmexpr] at hj
  have hj' := mul_le_mul_of_nonneg_left hj (le_of_lt hmR)
  have hrs : (m : ℝ) * ∑ i : Fin m, w i * (1 - p i) ^ n =
      ∑ i : Fin m, (1 - p i) ^ n := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [w]
    field_simp
  rw [hrs] at hj'
  simp only [PayOnce.success, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]
  nlinarith

theorem capacity_success_gap_pos (n m c : ℕ) (hm : 0 < m) (hc : c < m) :
    0 < 1 - PayOnce.success n ((c : ℝ) / m) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hcm : (c : ℝ) < m := by exact_mod_cast hc
  have hbase : 0 < 1 - (c : ℝ) / m := sub_pos.mpr ((div_lt_one hmR).mpr hcm)
  simpa [PayOnce.success] using pow_pos hbase n
end FloorCarrier
end FCAppendix.Existence.PayOnceBounded
