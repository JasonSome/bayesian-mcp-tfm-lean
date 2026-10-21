import FCAppendix.Affine.ClippedResidualKernel
import FCAppendix.Existence.Potential

noncomputable section
namespace FCAppendix.Affine.EqualCapacity
open Set MeasureTheory Classical
open scoped BigOperators

def demand (ξ b z : ℝ) : ℝ := max 0 (min 1 ((1-z/b)/ξ))

def ScalarThreshold (ξ b z p : ℝ) : Prop :=
  0≤p ∧ p≤1 ∧ (p=0→b*(1-ξ*p)≤z) ∧
    (p=1→z≤b*(1-ξ*p)) ∧ (0<p→p<1→b*(1-ξ*p)=z)

lemma demand_bounds (ξ b z : ℝ) : 0≤demand ξ b z ∧ demand ξ b z≤1 :=
  ⟨le_max_left _ _,max_le zero_le_one (min_le_left _ _)⟩

theorem demand_spec {ξ b : ℝ} (hξ : 0<ξ) (_hξ1 : ξ<1) (hb : 0<b) (z : ℝ) :
    ScalarThreshold ξ b z (demand ξ b z) := by
  have hp := demand_bounds ξ b z
  by_cases hh : b≤z
  · have hr : (1-z/b)/ξ≤0 := div_nonpos_of_nonpos_of_nonneg
      (by have ht : (1:ℝ)≤z/b := (le_div_iff₀ hb).2 (by simpa only [one_mul] using hh); linarith) hξ.le
    have he : demand ξ b z=0 := by
      unfold demand
      rw [min_eq_right (hr.trans zero_le_one),max_eq_left hr]
    refine ⟨hp.1,hp.2,?_,?_,?_⟩
    · intro _; simpa only [he,mul_zero,sub_zero,mul_one] using hh
    · intro h; rw [he] at h; norm_num at h
    · intro h; rw [he] at h; linarith
  · by_cases hl : z≤(1-ξ)*b
    · have hr : 1≤(1-z/b)/ξ := (le_div_iff₀ hξ).2 (by
        have ht := (div_le_iff₀ hb).2 hl
        linarith)
      have he : demand ξ b z=1 := by simp [demand,min_eq_left hr]
      refine ⟨hp.1,hp.2,?_,?_,?_⟩
      · intro h; rw [he] at h; norm_num at h
      · intro _; simpa only [he,mul_one,mul_comm b] using hl
      · intro _ h; rw [he] at h; linarith
    · have hzlo : (1-ξ)*b<z := lt_of_not_ge hl
      have hzhi : z<b := lt_of_not_ge hh
      have hr0 : 0<(1-z/b)/ξ := div_pos
        (by have ht := (div_lt_one hb).2 hzhi; linarith) hξ
      have hr1 : (1-z/b)/ξ<1 := (div_lt_iff₀ hξ).2 (by
        have ht := (lt_div_iff₀ hb).2 hzlo
        linarith)
      have he : demand ξ b z=(1-z/b)/ξ := by
        simp only [demand,min_eq_right hr1.le,max_eq_right hr0.le]
      have hreceipt : b*(1-ξ*demand ξ b z)=z := by
        rw [he]
        field_simp [hξ.ne',hb.ne']
        ring
      exact ⟨hp.1,hp.2,(fun _=>hreceipt.le),(fun _=>hreceipt.ge),(fun _ _=>hreceipt)⟩

theorem continuous_demand (ξ b : ℝ) : Continuous (demand ξ b) := by
  unfold demand
  exact continuous_const.max (continuous_const.min
    ((continuous_const.sub (continuous_id.div_const b)).div_const ξ))

lemma demand_zero_price {ξ b : ℝ} (hξ : 0<ξ) (hξ1 : ξ<1) : demand ξ b 0=1 := by
  have hr : 1≤1/ξ := (le_div_iff₀ hξ).2 (by simpa only [one_mul] using hξ1.le)
  simp only [demand,zero_div,sub_zero]
  rw [min_eq_left hr,max_eq_right zero_le_one]

lemma demand_high_price {ξ b : ℝ} (hξ : 0<ξ) (hb : 0<b) {z : ℝ} (hz : b≤z) :
    demand ξ b z=0 := by
  have hr : (1-z/b)/ξ≤0 := div_nonpos_of_nonpos_of_nonneg
    (by have ht : (1:ℝ)≤z/b := (le_div_iff₀ hb).2 (by simpa only [one_mul] using hz); linarith) hξ.le
  unfold demand
  rw [min_eq_right (hr.trans zero_le_one),max_eq_left hr]

variable {ι : Type*} [Fintype ι]

def IsKernel (ξ : ℝ) (c : ℕ) (b p : ι→ℝ) : Prop :=
  (∀i,0≤p i) ∧ (∀i,p i≤1) ∧ (∑i,p i=(min c (Fintype.card ι):ℕ)) ∧
    ∃z,0≤z ∧ Proposer.Threshold p (fun i=>b i*(1-ξ*p i)) z

theorem exists_isKernel {ξ : ℝ} (hξ : 0<ξ) (hξ1 : ξ<1) (c : ℕ)
    (b : ι→ℝ) (hb : ∀i,0<b i) : ∃p,IsKernel ξ c b p := by
  let M : ℝ := 1+∑i,b i
  have hbM (i : ι) : b i≤M := by
    have hh := Finset.single_le_sum (s:=Finset.univ) (f:=b)
      (fun j _ =>(hb j).le) (Finset.mem_univ i)
    dsimp [M]
    linarith
  have hM : 0≤M := by
    have hh := Finset.sum_nonneg (s:=Finset.univ) (f:=b) (fun i _=>(hb i).le)
    dsimp [M]
    linarith
  let D : ℝ→ℝ := fun z=>∑i,demand ξ (b i) z
  have hcont : Continuous D := continuous_finsetSum _ (fun i _=>continuous_demand ξ (b i))
  have hD0 : D 0=(Fintype.card ι:ℝ) := by
    dsimp [D]
    simp only [demand_zero_price hξ hξ1,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
  have hDM : D M=0 := by
    dsimp [D]
    simp only [demand_high_price hξ (hb _) (hbM _),Finset.sum_const_zero]
  obtain ⟨z,hz,hroot⟩ := intermediate_value_Icc' hM hcont.continuousOn
    (show ((min c (Fintype.card ι):ℕ):ℝ)∈Icc (D M) (D 0) by
      rw [hDM,hD0]
      exact ⟨Nat.cast_nonneg _,Nat.cast_le.mpr (min_le_right _ _)⟩)
  refine ⟨fun i=>demand ξ (b i) z,?_,?_,hroot,z,hz.1,?_,?_,?_⟩
  · intro i; exact (demand_bounds ξ (b i) z).1
  · intro i; exact (demand_bounds ξ (b i) z).2
  · intro i hi; exact (demand_spec hξ hξ1 (hb i) z).2.2.1 hi
  · intro i hi; exact (demand_spec hξ hξ1 (hb i) z).2.2.2.1 hi
  · intro i hi hj; exact (demand_spec hξ hξ1 (hb i) z).2.2.2.2 hi hj

theorem isKernel_unique {ξ : ℝ} (hξ : 0<ξ) (c : ℕ) (b : ι→ℝ) (hb : ∀i,0<b i)
    (p q : ι→ℝ) (hp : IsKernel ξ c b p) (hq : IsKernel ξ c b q) : p=q := by
  obtain ⟨hp0,hp1,hps,z,hz,hpt⟩ := hp
  obtain ⟨hq0,hq1,hqs,z',hz',hqt⟩ := hq
  apply Proposer.unique_marginals (fun i x=>b i*(1-ξ*x)) _ p q z z'
    ((min c (Fintype.card ι):ℕ):ℝ) hp0 hp1 hps hq0 hq1 hqs hz hz' hpt hqt
  intro i x y _ hxy _
  have hh := mul_pos (hb i) (mul_pos hξ (sub_pos.mpr hxy))
  nlinarith

def kernelMarginal (ξ : ℝ) (c : ℕ) (b : ι→ℝ) : ι→ℝ :=
  if h : ∃p,IsKernel ξ c b p then h.choose else fun _=>0

theorem kernelMarginal_spec {ξ : ℝ} (hξ : 0<ξ) (hξ1 : ξ<1) (c : ℕ)
    (b : ι→ℝ) (hb : ∀i,0<b i) : IsKernel ξ c b (kernelMarginal ξ c b) := by
  have hh := exists_isKernel hξ hξ1 c b hb
  rw [kernelMarginal,dif_pos hh]
  exact hh.choose_spec
end FCAppendix.Affine.EqualCapacity
