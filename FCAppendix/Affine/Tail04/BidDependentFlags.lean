import FCAppendix.Probability.IndependentCounts
import FCAppendix.Probability.SimultaneousCongestion

noncomputable section
namespace FCAppendix.Affine.Tail04.BidDependentFlags
open Set Classical
open scoped BigOperators

variable {ι Ω Ξ : Type*} [Fintype ι] [DecidableEq ι] [Fintype Ω] [Fintype Ξ]

def product (μ : ι → FiniteLaw Ω) : FiniteLaw (ι → Ω) where
  mass ω := ∏ i, (μ i).mass (ω i)
  nonneg ω := Finset.prod_nonneg fun i _ => (μ i).nonneg (ω i)
  total := by
    rw [← Fintype.prod_sum (fun i ω => (μ i).mass ω)]
    simp only [FiniteLaw.total,Finset.prod_const_one]

theorem expect_product (μ : ι → FiniteLaw Ω) (f : ι → Ω → ℝ) :
    (product μ).expect (fun ω => ∏ i, f i (ω i)) = ∏ i, (μ i).expect (f i) := by
  unfold FiniteLaw.expect product
  simp_rw [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i ω => (μ i).mass ω*f i ω)).symm

theorem expect_coordinate (μ : ι → FiniteLaw Ω) (i : ι) (f : Ω → ℝ) :
    (product μ).expect (fun ω => f (ω i)) = (μ i).expect f := by
  have hprod (ω : ι → Ω) : (∏ j, if j=i then f (ω j) else 1) = f (ω i) := by simp
  calc
    _ = (product μ).expect (fun ω => ∏ j, if j=i then f (ω j) else 1) := by
      apply FiniteLaw.expect_congr
      intro ω
      exact (hprod ω).symm
    _ = ∏ j, (μ j).expect (fun ω => if j=i then f ω else 1) := expect_product μ (fun j z => if j=i then f z else 1)
    _ = _ := by
      have he (j : ι) : (μ j).expect (fun ω => if j=i then f ω else 1) =
          if j=i then (μ i).expect f else 1 := by
        by_cases hj : j=i <;> simp [hj]
      simp_rw [he]
      simp

set_option maxHeartbeats 800000 in
theorem map_product (μ : ι → FiniteLaw Ω) (f : ι → Ω → Ξ) :
    (product μ).map (fun ω i => f i (ω i)) = product (fun i => (μ i).map (f i)) := by
  apply FiniteLaw.ext
  intro y
  simp only [FiniteLaw.map,product]
  change (∑ ω : ι → Ω, if (fun i => f i (ω i)) = y then ∏ i, (μ i).mass (ω i) else 0) =
    ∏ i, ∑ v, if f i v = y i then (μ i).mass v else 0
  have he (ω : ι → Ω) :
      (if (fun i => f i (ω i)) = y then ∏ i, (μ i).mass (ω i) else 0) =
      ∏ i, if f i (ω i) = y i then (μ i).mass (ω i) else 0 := by
    by_cases h : ∀ i, f i (ω i) = y i
    · simp only [if_pos (funext h)]
      apply Finset.prod_congr rfl
      intro i _
      exact (if_pos (h i)).symm
    · obtain ⟨i,hi⟩ := not_forall.mp h
      have hn : (fun i => f i (ω i)) ≠ y := fun h => hi (congrFun h i)
      rw [if_neg hn]
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      exact if_neg hi
  simp_rw [he]
  exact (Fintype.prod_sum (fun i v => if f i v = y i then (μ i).mass v else 0)).symm

theorem map_equiv_mass (μ : FiniteLaw Ω) (e : Ω ≃ Ξ) (y : Ξ) :
    (μ.map e).mass y = μ.mass (e.symm y) := by
  change (∑ x, if e x=y then μ.mass x else 0) = _
  have he (x : Ω) : e x=y ↔ x=e.symm y := by
    constructor
    · intro h
      exact e.injective (h.trans (e.apply_symm_apply y).symm)
    · rintro rfl
      exact e.apply_symm_apply y
  simp_rw [he]
  simp

theorem product_group (μ : ι → FiniteLaw Ω) (ν : ι → FiniteLaw Ξ) :
    (product (fun i => (μ i).prod (ν i))).map
        (fun ω : ι → Ω×Ξ => (fun i => (ω i).1, fun i => (ω i).2)) =
      (product μ).prod (product ν) := by
  let e : (ι → Ω × Ξ) ≃ (ι → Ω) × (ι → Ξ) := {
    toFun := fun ω => (fun i => (ω i).1, fun i => (ω i).2)
    invFun := fun z i => (z.1 i,z.2 i)
    left_inv := by intro ω; funext i; exact Prod.eta _
    right_inv := by intro z; cases z; rfl }
  change (product (fun i => (μ i).prod (ν i))).map e = _
  apply FiniteLaw.ext
  intro z
  rw [map_equiv_mass]
  change (∏ i, (μ i).mass (z.1 i)*(ν i).mass (z.2 i)) =
    (∏ i, (μ i).mass (z.1 i))*(∏ i, (ν i).mass (z.2 i))
  exact Finset.prod_mul_distrib

theorem product_split (μ : ι → FiniteLaw Ω) (p : ι → Prop) [DecidablePred p] :
    (product μ).map (fun ω =>
      ((fun i : {i // p i} => ω i),(fun i : {i // ¬p i} => ω i))) =
      (product (fun i : {i // p i} => μ i)).prod
        (product (fun i : {i // ¬p i} => μ i)) := by
  let e : (ι → Ω) ≃ ({i // p i} → Ω) × ({i // ¬p i} → Ω) := {
    toFun := fun ω => (fun i => ω i,fun i => ω i)
    invFun := fun z i => if h : p i then z.1 ⟨i,h⟩ else z.2 ⟨i,h⟩
    left_inv := by intro ω; funext i; dsimp; split_ifs <;> rfl
    right_inv := by
      intro z
      apply Prod.ext
      · funext i
        simp only [dif_pos i.property]
      · funext i
        simp only [dif_neg i.property] }
  change (product μ).map e = _
  apply FiniteLaw.ext
  intro z
  rw [map_equiv_mass]
  change (∏ i, (μ i).mass (e.symm z i)) =
    (∏ i : {i // p i}, (μ i).mass (z.1 i))*
      (∏ i : {i // ¬p i}, (μ i).mass (z.2 i))
  rw [← Fintype.prod_subtype_mul_prod_subtype (p := p)
    (fun i => (μ i).mass (e.symm z i))]
  congr 1
  · apply Finset.prod_congr rfl
    intro i _
    change (μ i).mass (if h : p i then z.1 ⟨i,h⟩ else z.2 ⟨i,h⟩) = _
    rw [dif_pos i.property]
  · apply Finset.prod_congr rfl
    intro i _
    change (μ i).mass (if h : p i then z.1 ⟨i,h⟩ else z.2 ⟨i,h⟩) = _
    rw [dif_neg i.property]

theorem product_restrict (μ : ι → FiniteLaw Ω) (p : ι → Prop) [DecidablePred p] :
    (product μ).map (fun ω (i : {i // p i}) => ω i) =
      product (fun i : {i // p i} => μ i) := by
  apply FiniteLaw.ext_expect
  intro f
  rw [FiniteLaw.expect_map]
  have he := congrArg (fun law => law.expect (fun z => f z.1)) (product_split μ p)
  simpa only [FiniteLaw.expect_map,FiniteLaw.expect_prod,FiniteLaw.expect_const] using he

theorem flags_restrict (p : ι → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (active : ι → Prop) :
    (product (fun i => IndependentCounts.bernoulli (p i) (hp0 i) (hp1 i))).map
        (fun ω (i : {i // active i}) => ω i) =
      product (fun i : {i // active i} =>
        IndependentCounts.bernoulli (p i) (hp0 i) (hp1 i)) :=
  product_restrict _ active

def flags (p : ι → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) :
    FiniteLaw (ι → Bool) :=
  product fun i => IndependentCounts.bernoulli (p i) (hp0 i) (hp1 i)

theorem flags_mass (p : ι → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (ω : ι → Bool) :
    (flags p hp0 hp1).mass ω = ∏ i, if ω i then p i else 1-p i := rfl

theorem flag_probability (p : ι → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (i : ι) : (flags p hp0 hp1).prob (fun ω => ω i = true) = p i := by
  rw [FiniteLaw.prob_eq_expect,flags,expect_coordinate _ i (fun z : Bool => if z=true then (1:ℝ) else 0)]
  rw [FiniteLaw.expect_singleton]
  change (if true then p i else 1-p i)=p i
  rfl

def mixedProbability (β B b : ℝ) : ℝ := β*((B-b)/(B-1))^2

theorem mixedProbability_mem (β B b : ℝ)
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hB : 1 < B) (hb : b ∈ Icc 1 B) :
    mixedProbability β B b ∈ Icc (0:ℝ) 1 := by
  have hd : 0 < B-1 := by linarith
  have hq0 : 0 ≤ (B-b)/(B-1) := div_nonneg (by linarith [hb.2]) hd.le
  have hq1 : (B-b)/(B-1) ≤ 1 := (div_le_one hd).mpr (by linarith [hb.1])
  unfold mixedProbability
  constructor
  · positivity
  · have hs : ((B-b)/(B-1))^2 ≤ 1 := by nlinarith
    have hmul := mul_le_mul_of_nonneg_left hs hβ0
    nlinarith

def bidFlags (β B : ℝ) (b : ι → ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hB : 1 < B) (hb : ∀ i, b i ∈ Icc 1 B) : FiniteLaw (ι → Bool) :=
  flags (fun i => mixedProbability β B (b i))
    (fun i => (mixedProbability_mem β B (b i) hβ0 hβ1 hB (hb i)).1)
    (fun i => (mixedProbability_mem β B (b i) hβ0 hβ1 hB (hb i)).2)

theorem actual_bid_dependent_probability (β B : ℝ) (b : ι → ℝ)
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hB : 1 < B) (hb : ∀ i, b i ∈ Icc 1 B)
    (i : ι) :
    (bidFlags β B b hβ0 hβ1 hB hb).prob (fun ω => ω i=true) =
      β*((B-b i)/(B-1))^2 := flag_probability _ _ _ i

def remainderProbability (ε p : ℝ) : ℝ := (p-ε)/(1-2*ε)

theorem remainderProbability_mem (ε p : ℝ) (_hε : 0 < ε) (hε' : ε < 1/2)
    (hp : ε ≤ p) (hp' : p ≤ 1-ε) : remainderProbability ε p ∈ Icc (0:ℝ) 1 := by
  have hd : 0 < 1-2*ε := by linarith
  exact ⟨div_nonneg (sub_nonneg.mpr hp) hd.le,
    (div_le_one hd).mpr (by linarith)⟩

def thinningCoordinate (ε p : ℝ) (hε : 0 < ε) (hε' : ε < 1/2)
    (hp : ε ≤ p) (hp' : p ≤ 1-ε) : FiniteLaw (Bool × (Bool × Bool)) :=
  (IndependentCounts.bernoulli (2*ε) (by positivity) (by linarith)).prod
    ((IndependentCounts.bernoulli (1/2) (by norm_num) (by norm_num)).prod
      (IndependentCounts.bernoulli (remainderProbability ε p)
        (remainderProbability_mem ε p hε hε' hp hp').1
        (remainderProbability_mem ε p hε hε' hp hp').2))

def thinnedBit (ω : Bool × (Bool × Bool)) : Bool := if ω.1 then ω.2.1 else ω.2.2

theorem thinningCoordinate_map (ε p : ℝ) (hε : 0 < ε) (hε' : ε < 1/2)
    (hp : ε ≤ p) (hp' : p ≤ 1-ε) :
    (thinningCoordinate ε p hε hε' hp hp').map thinnedBit =
      IndependentCounts.bernoulli p (by linarith) (by linarith) := by
  apply FiniteLaw.ext_expect
  intro f
  rw [FiniteLaw.expect_map]
  simp only [thinningCoordinate,FiniteLaw.expect_prod,IndependentCounts.expect_bernoulli]
  simp only [thinnedBit, Bool.false_eq_true, ite_false, ite_true]
  unfold remainderProbability
  have hd : 1-2*ε ≠ 0 := by linarith
  field_simp [hd]
  ring

theorem fair_product_thinning (ε : ℝ) (p : ι → ℝ)
    (hε : 0 < ε) (hε' : ε < 1/2)
    (hp : ∀ i, ε ≤ p i) (hp' : ∀ i, p i ≤ 1-ε) :
    (product (fun i => thinningCoordinate ε (p i) hε hε' (hp i) (hp' i))).map
      (fun ω i => thinnedBit (ω i)) =
      flags p (fun i => by linarith [hp i]) (fun i => by linarith [hp' i]) := by
  unfold flags
  rw [map_product]
  congr 1
  funext i
  exact thinningCoordinate_map ε (p i) hε hε' (hp i) (hp' i)

theorem any_flag_le_sum (p : ι → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) :
    (flags p hp0 hp1).prob (fun ω => ∃ i, ω i=true) ≤ ∑ i, p i := by
  have hh := SimultaneousCongestion.prob_exists_le (flags p hp0 hp1)
    Finset.univ (fun i ω => ω i=true)
  simpa only [Finset.mem_univ,true_and,flag_probability] using hh

theorem owner_acceptance_lower (π : ℝ) (hπ0 : 0 ≤ π) (hπ1 : π ≤ 1)
    (accepts : (ι → Bool) → Prop)
    (haccept : ∀ ω, (∀ i, ω i=false) → accepts ω) :
    1-(Fintype.card ι:ℝ)*π ≤
      (flags (fun _ : ι => π) (fun _ => hπ0) (fun _ => hπ1)).prob accepts := by
  let law := flags (fun _ : ι => π) (fun _ => hπ0) (fun _ => hπ1)
  have hbad : law.prob (fun ω => ∃ i, ω i=true) ≤ (Fintype.card ι:ℝ)*π := by
    simpa [law] using any_flag_le_sum (fun _ : ι => π) (fun _ => hπ0) (fun _ => hπ1)
  have hsub : law.prob (fun ω => ¬∃ i, ω i=true) ≤ law.prob accepts := by
    apply law.prob_mono
    intro ω hω
    apply haccept ω
    intro i
    cases he : ω i
    · rfl
    · exact (hω ⟨i,he⟩).elim
  rw [law.prob_compl] at hsub
  linarith

end FCAppendix.Affine.Tail04.BidDependentFlags
