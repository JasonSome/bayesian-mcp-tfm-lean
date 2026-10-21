import FCAppendix.Affine.Hybrid.TypicalCountNeighborhood
import FCAppendix.Affine.Hybrid.UniformFiniteMenu

noncomputable section
namespace FCAppendix.Affine.Hybrid
open Set Filter Topology Classical

def normalizedOwnerShare (p : Fin 4 → ℝ) : ℝ := (2*p 2+p 3)/p 0

lemma normalizedFactor_count_eq {ξ : ℝ} (M A small ell gap : ℕ)
    (hM : 0 < M) (hsmall : ell < small) (hK : 2*ell+gap < A) :
    normalizedFactor ξ (finiteCountPoint M A small ell gap)=
      finiteReceiptFactor ξ (A-(2*ell+gap)) (small-ell) := by
  have hm : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hM.ne'
  have hd : ((A-(2*ell+gap) : ℕ) : ℝ)=(A : ℝ)-2*ell-gap := by
    rw [Nat.cast_sub hK.le]
    push_cast
    ring
  have hr : ((small-ell : ℕ) : ℝ)=(small : ℝ)-ell := Nat.cast_sub hsmall.le
  dsimp [normalizedFactor,normalizedMixed,normalizedResidual,finiteCountPoint,finiteReceiptFactor]
  rw [hd,hr]
  field_simp

lemma normalizedOwnerShare_count_eq (M A small ell gap : ℕ) (hM : 0 < M) (hA : 0 < A) :
    normalizedOwnerShare (finiteCountPoint M A small ell gap)=
      ((2*ell+gap : ℕ) : ℝ)/(A : ℝ) := by
  have hm : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hM.ne'
  have ha : (A : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hA.ne'
  dsimp [normalizedOwnerShare,finiteCountPoint]
  push_cast
  field_simp

theorem source_menu_neighborhood (a h ρ z ξ L U τ : ℝ)
    (ha : 0 < a) (hz : z < 1) (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (hq0 : 0 < sourceExposure a h ρ z) (hq1 : sourceExposure a h ρ z < 1)
    (hboxlo : (1-ξ)*U < (1-ξ*sourceExposure a h ρ z)*L)
    (hboxhi : (1-ξ*sourceExposure a h ρ z)*U < L) (hτ : 0 < τ) :
    {p : Fin 4 → ℝ | NormalizedGuardRegion ξ L U p ∧ a/2 < p 0 ∧
      a*(1-z)/2 < normalizedMixed p ∧ |normalizedOwnerShare p-z| < τ ∧
      |normalizedFactor ξ p-(1-ξ*sourceExposure a h ρ z)| < τ} ∈
      𝓝 (sourceCountPoint a h ρ z) := by
  let p₀ := sourceCountPoint a h ρ z
  have hdEq : normalizedMixed p₀=a*(1-z) := by dsimp [p₀,sourceCountPoint,normalizedMixed]; ring
  have hd : 0 < normalizedMixed p₀ := by rw [hdEq]; positivity
  have hqEq : normalizedResidual p₀/normalizedMixed p₀=sourceExposure a h ρ z := by
    rw [hdEq]
    dsimp [p₀,sourceCountPoint,normalizedResidual,sourceExposure]
    field_simp [ha.ne',(sub_pos.mpr hz).ne']
  have hfEq : normalizedFactor ξ p₀=1-ξ*sourceExposure a h ρ z := by rw [normalizedFactor,hqEq]
  have hsEq : normalizedOwnerShare p₀=z := by
    dsimp [normalizedOwnerShare,p₀,sourceCountPoint]
    field_simp
    ring
  have hdc : Continuous normalizedMixed := by unfold normalizedMixed; fun_prop
  have hrc : Continuous normalizedResidual := by unfold normalizedResidual; fun_prop
  have hfc : ContinuousAt (normalizedFactor ξ) p₀ :=
    continuousAt_const.sub (continuousAt_const.mul (hrc.continuousAt.div hdc.continuousAt hd.ne'))
  have hsc : ContinuousAt normalizedOwnerShare p₀ := by
    apply ContinuousAt.div
    · fun_prop
    · exact (continuous_apply 0).continuousAt
    · exact ha.ne'
  obtain ⟨η,hη,hηguard⟩ := exists_normalized_guard_neighborhood a h ρ z ξ L U
    ha hz hξ hξ1 hq0 hq1 hboxlo hboxhi
  have hg : {p : Fin 4 → ℝ | NormalizedGuardRegion ξ L U p} ∈ 𝓝 p₀ := by
    apply Metric.mem_nhds_iff.mpr
    refine ⟨η,hη,?_⟩
    intro p hp
    apply hηguard
    exact (dist_pi_lt_iff hη).mp hp
  have hse : ∀ᶠ p in 𝓝 p₀, |normalizedOwnerShare p-z| < τ := by
    simpa only [Real.dist_eq,hsEq] using (Metric.tendsto_nhds.mp hsc) τ hτ
  have hfe : ∀ᶠ p in 𝓝 p₀, |normalizedFactor ξ p-(1-ξ*sourceExposure a h ρ z)| < τ := by
    simpa only [Real.dist_eq,hfEq] using (Metric.tendsto_nhds.mp hfc) τ hτ
  have ha0 : a/2 < p₀ 0 := by change a/2 < a; linarith
  have hd0 : a*(1-z)/2 < normalizedMixed p₀ := by rw [hdEq]; linarith
  filter_upwards [hg,(continuous_apply 0).continuousAt.eventually (Ioi_mem_nhds ha0),
    hdc.continuousAt.eventually (Ioi_mem_nhds hd0),hse,hfe] with p hgp hap hdp hsp hfp
  exact ⟨hgp,hap,hdp,hsp,hfp⟩

end FCAppendix.Affine.Hybrid
