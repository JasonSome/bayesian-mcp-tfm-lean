import FCAppendix.Affine.Hybrid.FavoredInterimJump

noncomputable section
namespace FCAppendix.Affine.Hybrid
open MeasureTheory Set Filter Topology
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma ownerSetPayoff_affine_value (xi eta v : ℝ) (b : ι→ℝ) (r : ℕ) (i : ι) (E : Finset ι) :
    ownerSetPayoff xi eta v b r i E=
      v*(ownerSetPayoff xi eta 1 b r i E-ownerSetPayoff xi eta 0 b r i E)+
        ownerSetPayoff xi eta 0 b r i E := by
  unfold ownerSetPayoff independentTwo
  split_ifs <;> ring

lemma sourceOwnerPayoff_affine_value [Nonempty ι] (xi eta v : ℝ) (b : ι→ℝ)
    (r K1 K2 : ℕ) (i : ι) :
    sourceOwnerPayoff xi eta v b r K1 K2 i=
      v*(sourceOwnerPayoff xi eta 1 b r K1 K2 i-sourceOwnerPayoff xi eta 0 b r K1 K2 i)+
        sourceOwnerPayoff xi eta 0 b r K1 K2 i := by
  unfold sourceOwnerPayoff
  simp_rw [ownerSetPayoff_affine_value xi eta v]
  rw [FiniteLaw.expect_add,FiniteLaw.expect_const_mul,FiniteLaw.expect_sub]

lemma measurable_joint_sourceOwnerPayoff [Nonempty ι] (xi eta : ℝ) (r K1 K2 : ℕ) (i : ι) :
    Measurable (fun t : ℝ×(ι→ℝ)=>sourceOwnerPayoff xi eta t.1 t.2 r K1 K2 i) := by
  have he : (fun t : ℝ×(ι→ℝ)=>sourceOwnerPayoff xi eta t.1 t.2 r K1 K2 i)=
      (fun t : ℝ×(ι→ℝ)=>t.1*(sourceOwnerPayoff xi eta 1 t.2 r K1 K2 i-
        sourceOwnerPayoff xi eta 0 t.2 r K1 K2 i)+sourceOwnerPayoff xi eta 0 t.2 r K1 K2 i) := by
    funext t
    exact sourceOwnerPayoff_affine_value xi eta t.1 t.2 r K1 K2 i
  rw [he]
  exact (measurable_fst.mul (((measurable_sourceOwnerPayoff xi eta 1 r K1 K2 i).comp measurable_snd).sub
    ((measurable_sourceOwnerPayoff xi eta 0 r K1 K2 i).comp measurable_snd))).add
    ((measurable_sourceOwnerPayoff xi eta 0 r K1 K2 i).comp measurable_snd)

lemma continuousAt_joint_sourceOwnerPayoff [Nonempty ι] (xi eta : ℝ) (r K1 K2 : ℕ) (i : ι)
    (hN : 2≤Fintype.card ι) (hK0 : 0<K1+K2) (hKN : K1+K2<Fintype.card ι)
    (t : ℝ×(ι→ℝ)) (hb : ∀j,0<t.2 j) (hnotie : ∀j,j≠i→t.2 j≠t.2 i) :
    ContinuousAt (fun s : ℝ×(ι→ℝ)=>sourceOwnerPayoff xi eta s.1 s.2 r K1 K2 i) t := by
  have h0:=(continuousAt_sourceOwnerPayoff xi eta 0 t.2 r K1 K2 i hN hK0 hKN hb hnotie).comp
    (f:=Prod.snd) continuous_snd.continuousAt
  have h1:=(continuousAt_sourceOwnerPayoff xi eta 1 t.2 r K1 K2 i hN hK0 hKN hb hnotie).comp
    (f:=Prod.snd) continuous_snd.continuousAt
  have he : (fun t : ℝ×(ι→ℝ)=>sourceOwnerPayoff xi eta t.1 t.2 r K1 K2 i)=
      (fun t : ℝ×(ι→ℝ)=>t.1*(sourceOwnerPayoff xi eta 1 t.2 r K1 K2 i-
        sourceOwnerPayoff xi eta 0 t.2 r K1 K2 i)+sourceOwnerPayoff xi eta 0 t.2 r K1 K2 i) := by
    funext t
    exact sourceOwnerPayoff_affine_value xi eta t.1 t.2 r K1 K2 i
  rw [he]
  exact (continuous_fst.continuousAt.mul (h1.sub h0)).add h0

theorem exists_joint_sourceOwnerPayoff_box_bound [Nonempty ι]
    {L U vlo vhi : ℝ} (hL : 0<L) (xi eta : ℝ) (r K1 K2 : ℕ) (i : ι)
    (hN : 2≤Fintype.card ι) (hK0 : 0<K1+K2) (hKN : K1+K2<Fintype.card ι) :
    ∃C:ℝ,∀v∈Icc vlo vhi,∀b : ι→ℝ,(∀j,b j∈Icc L U)→
      ‖sourceOwnerPayoff xi eta v b r K1 K2 i‖≤C := by
  obtain ⟨C0,hC0⟩:=exists_sourceOwnerPayoff_box_bound hL xi eta 0 r K1 K2 i hN hK0 hKN
  obtain ⟨C1,hC1⟩:=exists_sourceOwnerPayoff_box_bound hL xi eta 1 r K1 K2 i hN hK0 hKN
  refine ⟨(|vlo|+|vhi|)*(|C1|+|C0|)+|C0|,?_⟩
  intro v hv b hb
  have h0 : |sourceOwnerPayoff xi eta 0 b r K1 K2 i|≤|C0| :=
    (hC0 b hb).trans (le_abs_self C0)
  have h1 : |sourceOwnerPayoff xi eta 1 b r K1 K2 i|≤|C1| :=
    (hC1 b hb).trans (le_abs_self C1)
  have hv' : |v|≤|vlo|+|vhi| := abs_le.mpr
    ⟨by linarith [hv.1,neg_abs_le vlo,abs_nonneg vhi],by linarith [hv.2,le_abs_self vhi,abs_nonneg vlo]⟩
  rw [Real.norm_eq_abs,sourceOwnerPayoff_affine_value xi eta v]
  calc
    _ ≤ |v| * (|sourceOwnerPayoff xi eta 1 b r K1 K2 i|+
        |sourceOwnerPayoff xi eta 0 b r K1 K2 i|)+|sourceOwnerPayoff xi eta 0 b r K1 K2 i| := by
      exact (abs_add_le _ _).trans (add_le_add
        (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (abs_sub _ _) (abs_nonneg _)) le_rfl)
    _ ≤ _ := add_le_add (mul_le_mul hv' (add_le_add h1 h0) (by positivity) (by positivity)) h0

end FCAppendix.Affine.Hybrid
