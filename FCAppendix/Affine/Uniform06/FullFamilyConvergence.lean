import FCAppendix.Affine.Uniform06.FullJointLaw

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.FullFamilyConvergence
open MeasureTheory Set Filter Topology
open Uniform07 LiteralExperiment LiteralPrefixStieltjes LiteralRankIC
open EarlyJointCompactness InactiveFamily FullJointLaw

section Family
variable (C : ℕ → Type*) (G : (m : ℕ) → C m → ProbabilityMeasure (ℝ × ℝ))
variable (g : (m : ℕ) → C m → GuardData)
variable (cm : (m : ℕ) → C m → (Fin (m-1) → Fin 4) → ℝ)

theorem source_family_weak_limit (i : Row) {K : ℝ} (hK : entry i < K)
    (hvalue : ∀ m (E : C m),(G m E:Measure (ℝ × ℝ)).map Prod.fst=
      LowChernoff.conditionalValueLaw i)
    (hatom : ∀ m (E : C m) b,((G m E:Measure (ℝ × ℝ)).map Prod.snd) {b}=0)
    (hcommon : ∀ m (E : C m),∀ᵐ p ∂(G m E:Measure (ℝ × ℝ)),
      p ∈ usedSet i m (G m E:Measure (ℝ × ℝ)) (g m E) (cm m E) (ReceiptGap.cap i))
    (hactive : ∀ a > (0:ℝ),∀ e > (0:ℝ),∀ᶠ m in atTop,∀ E : C m,
      ∀ᵐ p ∂(G m E:Measure (ℝ × ℝ)),p.1 ∈ Ioc (entry i+a) (cutoff i) →
        |p.2-ActiveGraphComponent.activeBid i p.1| ≤ e)
    (hroot : ∀ ε > (0:ℝ),∀ᶠ m in atTop,∀ E : C m,
      |(g m E).multiplier-entry i| < ε)
    (hguard : ∀ᶠ m in atTop,∀ E : C m,(g m E).radius ≤ cutoff i/100 ∧
      PrefixConditions (xi i) (g m E) K) :
    ∀ V ∈ 𝓝 (law i),∀ᶠ m in atTop,∀ E : C m,G m E ∈ V := by
  classical
  have hbox : ∀ m (E : C m),∀ᵐ p ∂(G m E:Measure (ℝ × ℝ)),
      p ∈ box (cutoff i) (ReceiptGap.cap i) := by
    intro m E
    exact (hcommon m E).mono fun p hp => ⟨hp.1,hp.2.1.le,hp.2.2.1.2.trans (min_le_right _ _)⟩
  have hi : ∀ d > (0:ℝ),d ≤ x i-1/2 → ∀ e > (0:ℝ),∀ᶠ m in atTop,∀ E : C m,
      ∀ᵐ p ∂(G m E:Measure (ℝ × ℝ)),p.1 ≤ (x i-d)*cutoff i → |p.2-p.1| < e := by
    intro d hd hdmax e he
    filter_upwards [common_used_inactive C G g cm i hK hvalue hatom hcommon
      hactive hroot hguard hd hdmax he] with m hm E
    exact (hcommon m E).mono fun p hp hpv => hm E p hp hpv
  intro V hV
  by_contra h
  have hb (n : ℕ) : ∃ m ≥ n,∃ E : C m,G m E ∉ V := by
    by_contra hn
    push Not at hn
    exact h (eventually_atTop.mpr ⟨n,hn⟩)
  choose m hm E hbad using hb
  have hmlim : Tendsto m atTop atTop := by
    apply tendsto_atTop.mpr
    intro M
    exact eventually_atTop.mpr ⟨M,fun n hn => hn.trans (hm n)⟩
  let GG := fun n => G (m n) (E n)
  obtain ⟨G0,φ,hφ,hG0,_⟩ := exists_joint_subsequence GG (fun n => hbox _ _)
  have hmφ : Tendsto (m ∘ φ) atTop atTop := hmlim.comp hφ.tendsto_atTop
  have ha : ∀ a > (0:ℝ),∀ e > (0:ℝ),∀ᶠ n in atTop,
      ∀ᵐ p ∂(GG (φ n):Measure (ℝ × ℝ)),p.1 ∈ Ioc (entry i+a) (cutoff i) →
        |p.2-ActiveGraphComponent.activeBid i p.1| ≤ e := by
    intro a ha e he
    filter_upwards [hmφ.eventually (hactive a ha e he)] with n hn
    exact hn (E (φ n))
  have hi' : ∀ d > (0:ℝ),d ≤ x i-1/2 → ∀ e > (0:ℝ),∀ᶠ n in atTop,
      ∀ᵐ p ∂(GG (φ n):Measure (ℝ × ℝ)),p.1 ≤ (x i-d)*cutoff i → |p.2-p.1| < e := by
    intro d hd hdmax e he
    filter_upwards [hmφ.eventually (hi d hd hdmax e he)] with n hn
    exact hn (E (φ n))
  have hEq := full_limit_eq i (GG ∘ φ) G0 hG0 (fun n => hvalue _ _)
    (fun n => hbox _ _) ha hi'
  rw [hEq] at hG0
  obtain ⟨n,hn⟩ := (hG0.eventually hV).exists
  exact hbad (φ n) hn

theorem every_dependent_selection_tendsto (i : Row)
    (hu : ∀ V ∈ 𝓝 (law i),∀ᶠ m in atTop,∀ E : C m,G m E ∈ V)
    (E : (m : ℕ) → C m) : Tendsto (fun m => G m (E m)) atTop (𝓝 (law i)) := by
  apply tendsto_def.mpr
  intro V hV
  filter_upwards [hu V hV] with m hm
  exact hm (E m)

end Family
end FCAppendix.Affine.Uniform06.FullFamilyConvergence
