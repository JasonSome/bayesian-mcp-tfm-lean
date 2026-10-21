import FCAppendix.Affine.Tail04.ActualFallbackPromotion
import FCAppendix.Affine.Hybrid.FavoredInterimJump

noncomputable section
namespace FCAppendix.Affine.Tail04.UniformFallbackVariation
open MeasureTheory Set Filter Topology Classical
open TypicalFinitePromotion
open scoped BigOperators

lemma finite_expect_comm {A B : Type*} [Fintype A] [Fintype B]
    (μ : FiniteLaw A) (ν : FiniteLaw B) (f : A → B → ℝ) :
    μ.expect (fun a => ν.expect (f a))=ν.expect (fun b => μ.expect (fun a => f a b)) := by
  simp only [FiniteLaw.expect,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [Nonempty ι] in
theorem conditionalUtility_dirac_average (P : TypicalCountParameters)
    (phi : ℕ → ℝ → unitInterval) (e0 B eta v : ℝ)
    (he0 : 0≤ eta) (he1 : eta≤1) (i target : ι) (K : CountLaw 2) (b : ι → ℝ) :
    conditionalUtility P phi e0 B eta v he0 he1 i K b target=
      K.expect (fun r : Fin 3 => conditionalUtility P phi e0 B eta v he0 he1 i
        (FiniteLaw.dirac r) b target) := by
  simp only [conditionalUtility,affineCountUtility,CountLaw.utility,conditionalTargetCount,
    FiniteLaw.expect_finiteMix,FiniteLaw.expect_mixture,FiniteLaw.expect_dirac]
  rw [finite_expect_comm K]
  apply FiniteLaw.expect_congr
  intro z
  simp only [FiniteLaw.expect_add,FiniteLaw.expect_const_mul,FiniteLaw.expect_const]

def uniformVariation (P : TypicalCountParameters) (phi : ℕ → ℝ → unitInterval)
    (e0 B eta v : ℝ) (he0 : 0≤ eta) (he1 : eta≤1) (i : ι) (b d : ι → ℝ) : ℝ :=
  ∑ r : Fin 3,variation (conditionalUtility P phi e0 B eta v he0 he1 i (FiniteLaw.dirac r)) b d

omit [Nonempty ι] in
lemma uniformVariation_nonneg (P : TypicalCountParameters) (phi : ℕ → ℝ → unitInterval)
    (e0 B eta v : ℝ) (he0 : 0≤ eta) (he1 : eta≤1) (i : ι) (b d : ι → ℝ) :
    0≤ uniformVariation P phi e0 B eta v he0 he1 i b d :=
  Finset.sum_nonneg (fun _ _ => variation_nonneg _ _ _)

omit [Nonempty ι] in

theorem variation_le_uniformVariation (P : TypicalCountParameters)
    (phi : ℕ → ℝ → unitInterval) (e0 B eta v : ℝ)
    (he0 : 0≤ eta) (he1 : eta≤1) (i : ι) (K : CountLaw 2) (b d : ι → ℝ) :
    variation (conditionalUtility P phi e0 B eta v he0 he1 i K) b d≤
      uniformVariation P phi e0 B eta v he0 he1 i b d := by
  unfold uniformVariation variation
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro target _
  rw [conditionalUtility_dirac_average P phi e0 B eta v he0 he1 i target K b,
    conditionalUtility_dirac_average P phi e0 B eta v he0 he1 i target K d,
    ←FiniteLaw.expect_sub]
  exact Hybrid.abs_finite_expect_le_sum K _

omit [Nonempty ι] in

theorem dirac_variation_tendsto_zero (P : TypicalCountParameters)
    (phi : ℕ → ℝ → unitInterval)
    (hphi : ∀ M W,0< W → ContinuousAt (fun W' => (phi M W':ℝ)) W)
    (e0 B eta : ℝ) (he0 : 0≤ eta) (he1 : eta≤1) (i : ι) (r : Fin 3)
    (v : ℕ → ℝ) (b d : ℕ → ι → ℝ) (v0 : ℝ) (x : ι → ℝ)
    (hx : ∀ j,0< x j) (hv : Tendsto v atTop (𝓝 v0))
    (hb : Tendsto b atTop (𝓝 x)) (hd : Tendsto d atTop (𝓝 x)) :
    Tendsto (fun n => variation
      (conditionalUtility P phi e0 B eta (v n) he0 he1 i (FiniteLaw.dirac r))
      (b n) (d n)) atTop (𝓝 0) := by
  have hc (j : ι) : ContinuousAt
      (fun p : ℝ×(ι → ℝ) => conditionalUtility P phi e0 B eta p.1 he0 he1 i
        (FiniteLaw.dirac r) p.2 j) (v0,x) :=
    continuousAt_joint_conditionalTargetUtility P phi hphi e0 B eta he0 he1
      j i (FiniteLaw.dirac r) (v0,x) hx
  have he (j : ι) := ((hc j).tendsto.comp (hv.prodMk_nhds hb)).sub
    ((hc j).tendsto.comp (hv.prodMk_nhds hd))
  have hs := tendsto_finsetSum Finset.univ (fun j _ => (he j).abs)
  simpa only [variation,Function.comp_apply,sub_self,abs_zero,Finset.sum_const_zero] using hs

omit [Nonempty ι] in
theorem uniformVariation_tendsto_zero (P : TypicalCountParameters)
    (phi : ℕ → ℝ → unitInterval)
    (hphi : ∀ M W,0< W → ContinuousAt (fun W' => (phi M W':ℝ)) W)
    (e0 B eta : ℝ) (he0 : 0≤ eta) (he1 : eta≤1) (i : ι)
    (v : ℕ → ℝ) (b d : ℕ → ι → ℝ) (v0 : ℝ) (x : ι → ℝ)
    (hx : ∀ j,0< x j) (hv : Tendsto v atTop (𝓝 v0))
    (hb : Tendsto b atTop (𝓝 x)) (hd : Tendsto d atTop (𝓝 x)) :
    Tendsto (fun n => uniformVariation P phi e0 B eta (v n) he0 he1 i (b n) (d n))
      atTop (𝓝 0) := by
  have h := tendsto_finsetSum Finset.univ (fun r _ =>
    dirac_variation_tendsto_zero P phi hphi e0 B eta he0 he1 i r v b d v0 x hx hv hb hd)
  simpa only [uniformVariation,Finset.sum_const_zero] using h

omit [Nonempty ι] in

theorem arbitrary_fallback_variation_tendsto_zero (P : TypicalCountParameters)
    (phi : ℕ → ℝ → unitInterval)
    (hphi : ∀ M W,0< W → ContinuousAt (fun W' => (phi M W':ℝ)) W)
    (e0 B eta : ℝ) (he0 : 0≤ eta) (he1 : eta≤1) (i : ι) (K : ℕ → CountLaw 2)
    (v : ℕ → ℝ) (b d : ℕ → ι → ℝ) (v0 : ℝ) (x : ι → ℝ)
    (hx : ∀ j,0< x j) (hv : Tendsto v atTop (𝓝 v0))
    (hb : Tendsto b atTop (𝓝 x)) (hd : Tendsto d atTop (𝓝 x)) :
    Tendsto (fun n => variation (conditionalUtility P phi e0 B eta (v n) he0 he1 i (K n))
      (b n) (d n)) atTop (𝓝 0) := by
  apply squeeze_zero (fun n => variation_nonneg _ _ _)
    (fun n => variation_le_uniformVariation P phi e0 B eta (v n) he0 he1 i (K n) (b n) (d n))
  exact uniformVariation_tendsto_zero P phi hphi e0 B eta he0 he1 i v b d v0 x hx hv hb hd

end FCAppendix.Affine.Tail04.UniformFallbackVariation
