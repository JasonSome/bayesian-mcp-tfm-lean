import FCAppendix.Existence.Potential

noncomputable section
namespace FCAppendix.Existence.NarrowPayOnce
open Set CommonList PayOnce Proposer
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [Nonempty ι]

theorem exists_coordinate_le_average (p : ι → ℝ) (rho : ℝ)
    (hsum : ∑ i, p i=(Fintype.card ι:ℝ)*rho) : ∃ i, p i ≤ rho := by
  classical
  by_contra hh
  push Not at hh
  have hs : (∑ _i : ι, rho)<∑ i, p i := by
    apply Finset.sum_lt_sum (fun i _ => (hh i).le)
    obtain ⟨i⟩ := (inferInstance : Nonempty ι)
    exact ⟨i,Finset.mem_univ i,hh i⟩
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,hsum,lt_self_iff_false] at hs

theorem exists_coordinate_ge_average (p : ι → ℝ) (rho : ℝ)
    (hsum : ∑ i, p i=(Fintype.card ι:ℝ)*rho) : ∃ i, rho ≤ p i := by
  obtain ⟨i,hi⟩ := exists_coordinate_le_average (fun i => -p i) (-rho) (by
    simpa only [Finset.sum_neg_distrib,mul_neg] using congrArg Neg.neg hsum)
  exact ⟨i,by simpa only [neg_le_neg_iff] using hi⟩

theorem kernel_price_bracket {n c : ℕ} (hn : 2 ≤ n) {b p : ι → ℝ}
    {rho lower upper L : ℝ} (hrho : rho ∈ Ioo (0:ℝ) 1)
    (hb : ∀ i, 0<b i) (hband : ∀ i, lower ≤ b i ∧ b i ≤ upper)
    (hp : IsKernel n c b p) (hcap : (c:ℝ)=(Fintype.card ι:ℝ)*rho)
    (hc : c ≤ Fintype.card ι) (hL : Threshold p (fun i => b i*H n (p i)) L) :
    lower*H n rho ≤ L ∧ L ≤ upper*H n rho := by
  have hsum : (∑ i, p i)=(Fintype.card ι:ℝ)*rho := by
    rw [hp.2.2.1,Nat.min_eq_left hc,hcap]
  obtain ⟨i,hi⟩ := exists_coordinate_le_average p rho hsum
  obtain ⟨j,hj⟩ := exists_coordinate_ge_average p rho hsum
  have hH0 := (H_pos n (by omega) rho hrho.1.le hrho.2.le).le
  have hlo := scalar_receipt_le_of_lt_one n (b i) L (p i)
    ⟨hp.1 i,hp.2.1 i,hL.1 i,hL.2.1 i,hL.2.2 i⟩ (hi.trans_lt hrho.2)
  have hhi := scalar_price_le_of_pos n (b j) L (p j)
    ⟨hp.1 j,hp.2.1 j,hL.1 j,hL.2.1 j,hL.2.2 j⟩ (hrho.1.trans_le hj)
  constructor
  · exact (mul_le_mul_of_nonneg_right (hband i).1 hH0).trans
      ((mul_le_mul_of_nonneg_left (H_antitone n _ _ hi hrho.2.le) (hb i).le).trans hlo)
  · exact hhi.trans ((mul_le_mul_of_nonneg_left (H_antitone n _ _ hj (hp.2.1 j)) (hb j).le).trans
      (mul_le_mul_of_nonneg_right (hband j).2 hH0))

theorem kernelMarginal_uniform_difference {n c : ℕ} (hn : 2 ≤ n) (hc : c ≤ Fintype.card ι)
    {B rho eps : ℝ} (hrho : rho ∈ Ioo (0:ℝ) 1) (heps : 0 ≤ eps) (hB : eps<B)
    (hcap : (Fintype.card ι:ℝ)*rho=c) (b : ι → ℝ) (hband : ∀ i, |b i-B| ≤ eps) (i : ι) :
    |kernelMarginal n c b i-rho| ≤ 2*(n:ℝ)*eps/(B-eps) := by
  have hbounds (i : ι) : B-eps ≤ b i ∧ b i ≤ B+eps := by
    have hi := abs_le.mp (hband i)
    constructor <;> linarith
  have hb (i : ι) : 0<b i := (sub_pos.mpr hB).trans_le (hbounds i).1
  let p := kernelMarginal n c b
  have hp := kernelMarginal_spec n hn c b hb
  obtain ⟨L,_hL,ht⟩ := hp.2.2.2
  have hprice := kernel_price_bracket hn hrho hb hbounds hp hcap.symm hc ht
  have hH := H_bounds n (by omega) rho hrho.1.le hrho.2.le
  have hH0 := (H_pos n (by omega) rho hrho.1.le hrho.2.le).le
  have hbiLo := mul_le_mul_of_nonneg_right (hbounds i).1 hH0
  have hbiHi := mul_le_mul_of_nonneg_right (hbounds i).2 hH0
  have htwo : 2*eps*H n rho ≤ 2*eps := by nlinarith
  have habs : |L-b i*H n rho| ≤ 2*eps := by
    apply abs_le.mpr
    constructor <;> nlinarith [hprice.1,hprice.2]
  have hscalar : ScalarThreshold n (b i) L (p i) :=
    ⟨hp.1 i,hp.2.1 i,ht.1 i,ht.2.1 i,ht.2.2 i⟩
  have href : ScalarThreshold n (b i) (b i*H n rho) rho :=
    ⟨hrho.1.le,hrho.2.le,fun _ => le_rfl,fun _ => le_rfl,fun _ _ => rfl⟩
  have hs := (scalar_difference_bound n hn (b i) (hb i) L (b i*H n rho) (p i) rho hscalar href).trans habs
  have hnR : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hmul := mul_le_mul_of_nonneg_right hs hnR.le
  have he : b i/(n:ℝ)*|p i-rho| *(n:ℝ)=b i*|p i-rho| := by field_simp
  rw [he] at hmul
  apply (le_div_iff₀ (sub_pos.mpr hB)).mpr
  have hlow := mul_le_mul_of_nonneg_right (hbounds i).1 (abs_nonneg (p i-rho))
  nlinarith

theorem exists_uniform_kernel_radius {n : ℕ} (hn : 2 ≤ n) {B eta : ℝ}
    (hB : 0<B) (heta : 0<eta) :
    ∃ eps : ℝ, 0<eps ∧ eps<B ∧
      ∀ (κ : Type*) [Fintype κ] [Nonempty κ] (c : ℕ) (rho : ℝ),
      rho ∈ Ioo (0:ℝ) 1 → c ≤ Fintype.card κ → (Fintype.card κ:ℝ)*rho=c →
      ∀ b : κ → ℝ, (∀ i, |b i-B| ≤ eps) → ∀ i,
      |kernelMarginal n c b i-rho|<eta := by
  let eps := min (B/4) (eta*B/(16*(n:ℝ)))
  have hnR : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have heps : 0<eps := lt_min (by positivity) (by positivity)
  have heps1 : eps ≤ B/4 := min_le_left _ _
  have heps2 : eps ≤ eta*B/(16*(n:ℝ)) := min_le_right _ _
  have hepsB : eps<B := heps1.trans_lt (by linarith)
  have hbound : 2*(n:ℝ)*eps/(B-eps)<eta := by
    apply (div_lt_iff₀ (sub_pos.mpr hepsB)).mpr
    have hsmall := (le_div_iff₀ (by positivity : (0:ℝ)<16*(n:ℝ))).mp heps2
    have hmargin := mul_le_mul_of_nonneg_left heps1 heta.le
    nlinarith
  refine ⟨eps,heps,hepsB,?_⟩
  intro κ _ _ c rho hrho hc hcap b hb i
  exact (kernelMarginal_uniform_difference hn hc hrho heps.le hepsB hcap b hb i).trans_lt hbound

end FCAppendix.Existence.NarrowPayOnce
