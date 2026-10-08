import FCAppendix.Ample.DownstreamNormalizationCore

open Filter MeasureTheory Set
open scoped Topology ENNReal

namespace FCAppendix.Ample.DownstreamNormalizationCore

universe u v

theorem normalized_bid_error {X Y R F δ : ℝ}
    (hδ : 0 ≤ δ) (hδhalf : δ ≤ 1 / 2)
    (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (hRlo : 1 - δ ≤ R) (hRhi : R ≤ 1)
    (hF : |F - 1| ≤ δ) (hYsmall : Y ≤ δ)
    (hEq : F = Y + X * R) :
    |X - 1| ≤ 4 * δ := by
  rcases abs_le.mp hF with ⟨hFL, hFU⟩
  have hXRhi : X * R ≤ X := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hRhi hX
  have hXRlo : X * (1 - δ) ≤ X * R :=
    mul_le_mul_of_nonneg_left hRlo hX
  have hXlow : 1 - 2 * δ ≤ X := by linarith
  have hupper : X * (1 - δ) ≤ 1 + δ := by linarith
  have hprod : 0 ≤ δ * (1 / 2 - δ) :=
    mul_nonneg hδ (sub_nonneg.mpr hδhalf)
  have hcompare : 1 + δ ≤ (1 + 4 * δ) * (1 - δ) := by
    nlinarith
  have hden : 0 < 1 - δ := by linarith
  have hXupper : X ≤ 1 + 4 * δ :=
    (mul_le_mul_iff_left₀ hden).mp (hupper.trans hcompare)
  apply abs_le.mpr
  constructor <;> linarith

section Probability

variable {Ω : ℕ → Type u} [∀ m, MeasurableSpace (Ω m)]

theorem probZero_value_mul
    (μ : (m : ℕ) → Measure (Ω m))
    (V D : (m : ℕ) → Ω m → ℝ) {ell : ℝ}
    (hCompact : CompactContainment μ V ell)
    (hD : ProbZero μ D) :
    ProbZero μ (fun m ω => V m ω * D m ω) := by
  intro ε hε η hη
  obtain ⟨a, b, _ha, _hab, htail⟩ := hCompact (η / 2) (by linarith)
  let L : ℝ := max |a| |b| + 1
  have hL : 0 < L := by
    dsimp [L]
    have := le_max_left |a| |b|
    have := abs_nonneg a
    linarith
  have hδ : 0 < ε / L := div_pos hε hL
  filter_upwards [hD (ε / L) hδ (η / 2) (by linarith)] with m hm
  have hsub :
      {ω | ε < |V m ω * D m ω|} ⊆
        {ω | V m ω < a ∨ b < V m ω} ∪ {ω | ε / L < |D m ω|} := by
    intro ω hω
    by_cases htailω : V m ω < a ∨ b < V m ω
    · exact Or.inl htailω
    right
    by_contra hDω
    have hDle : |D m ω| ≤ ε / L := le_of_not_gt hDω
    have haV : a ≤ V m ω := le_of_not_gt (fun h => htailω (Or.inl h))
    have hVb : V m ω ≤ b := le_of_not_gt (fun h => htailω (Or.inr h))
    have hVa : |V m ω| ≤ L := by
      have hma : |a| ≤ max |a| |b| := le_max_left _ _
      have hmb : |b| ≤ max |a| |b| := le_max_right _ _
      have hna : -|a| ≤ a := neg_abs_le a
      have hbb : b ≤ |b| := le_abs_self b
      dsimp [L]
      apply abs_le.mpr
      constructor <;> linarith
    have hbound : |V m ω * D m ω| ≤ ε := by
      calc
        |V m ω * D m ω| = |V m ω| * |D m ω| := abs_mul _ _
        _ ≤ L * (ε / L) :=
          mul_le_mul hVa hDle (abs_nonneg _) (le_of_lt hL)
        _ = ε := by field_simp [ne_of_gt hL]
    exact (not_lt_of_ge hbound) hω
  calc
    μ m {ω | ε < |V m ω * D m ω|}
        ≤ μ m ({ω | V m ω < a ∨ b < V m ω} ∪
          {ω | ε / L < |D m ω|}) := measure_mono hsub
    _ ≤ μ m {ω | V m ω < a ∨ b < V m ω} +
          μ m {ω | ε / L < |D m ω|} := measure_union_le _ _
    _ < ENNReal.ofReal (η / 2) + ENNReal.ofReal (η / 2) :=
      ENNReal.add_lt_add (htail m) hm
    _ = ENNReal.ofReal η := by
      rw [← ENNReal.ofReal_add (by linarith : 0 ≤ η / 2) (by linarith : 0 ≤ η / 2)]
      congr 1
      ring

theorem probZero_bid_of_identity
    (μ : (m : ℕ) → Measure (Ω m))
    (X Y R F : (m : ℕ) → Ω m → ℝ)
    (hF : ProbZero μ (fun m ω => F m ω - 1))
    (hY : ProbZero μ Y)
    (hR : ProbZero μ (fun m ω => R m ω - 1))
    (hAlg : ∀ m, ∀ᵐ ω ∂μ m,
      0 ≤ X m ω ∧ 0 ≤ Y m ω ∧ R m ω ≤ 1 ∧
        F m ω = Y m ω + X m ω * R m ω) :
    ProbZero μ (fun m ω => X m ω - 1) := by
  intro ε hε η hη
  let δ : ℝ := min (ε / 8) (1 / 4)
  have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
  have hδhalf : δ ≤ 1 / 2 :=
    le_trans (min_le_right _ _) (by norm_num)
  have hδε : 4 * δ < ε := by
    have hδeps : δ ≤ ε / 8 := min_le_left _ _
    linarith
  filter_upwards
    [hF δ hδ (η / 3) (by linarith),
     hY δ hδ (η / 3) (by linarith),
     hR δ hδ (η / 3) (by linarith)] with m hmF hmY hmR
  let EF : Set (Ω m) := {ω | δ < |F m ω - 1|}
  let EY : Set (Ω m) := {ω | δ < |Y m ω|}
  let ER : Set (Ω m) := {ω | δ < |R m ω - 1|}
  have hsub : ∀ᵐ ω ∂μ m,
      ω ∈ {ω | ε < |X m ω - 1|} → ω ∈ (EF ∪ EY) ∪ ER := by
    filter_upwards [hAlg m] with ω hω
    intro hbad
    by_cases hf : δ < |F m ω - 1|
    · exact Or.inl (Or.inl hf)
    by_cases hy : δ < |Y m ω|
    · exact Or.inl (Or.inr hy)
    by_cases hr : δ < |R m ω - 1|
    · exact Or.inr hr
    have hFle : |F m ω - 1| ≤ δ := le_of_not_gt hf
    have hYle : Y m ω ≤ δ := (le_abs_self _).trans (le_of_not_gt hy)
    have hRlo : 1 - δ ≤ R m ω := by
      have hrl := (abs_le.mp (le_of_not_gt hr)).1
      linarith
    have hbound := normalized_bid_error (le_of_lt hδ) hδhalf
      hω.1 hω.2.1 hRlo hω.2.2.1 hFle hYle hω.2.2.2
    exact False.elim (not_lt_of_ge (le_trans hbound (le_of_lt hδε)) hbad)
  calc
    μ m {ω | ε < |X m ω - 1|} ≤ μ m ((EF ∪ EY) ∪ ER) :=
      measure_mono_ae hsub
    _ ≤ (μ m EF + μ m EY) + μ m ER :=
      (measure_union_le _ _).trans
        (add_le_add (measure_union_le _ _) le_rfl)
    _ < (ENNReal.ofReal (η / 3) + ENNReal.ofReal (η / 3)) +
          ENNReal.ofReal (η / 3) :=
      ENNReal.add_lt_add (ENNReal.add_lt_add hmF hmY) hmR
    _ = ENNReal.ofReal η := by
      rw [← ENNReal.ofReal_add (by linarith : 0 ≤ η / 3) (by linarith : 0 ≤ η / 3)]
      rw [← ENNReal.ofReal_add (by linarith : 0 ≤ η / 3 + η / 3)
        (by linarith : 0 ≤ η / 3)]
      congr 1
      ring

theorem payment_normalization_identity {fV V d B S K C : ℝ}
    (hS0 : 0 ≤ S) (hSK : S ≤ K) (hC : 0 < C)
    (hcost : fV = V * d + B * S) :
    fV / C = V * (d / C) + (K * B / C) * (S / K) := by
  by_cases hK : K = 0
  · have hS : S = 0 := le_antisymm (hSK.trans_eq hK) hS0
    rw [hcost, hK, hS]
    simp only [mul_zero, add_zero, zero_mul, zero_div, div_zero]
    ring
  · rw [hcost]
    field_simp [hK, ne_of_gt hC]

variable {A : ℕ → Type v}

theorem acceptance_probZero_of_upstream
    (μ : (m : ℕ) → Measure (Ω m))
    (M : (m : ℕ) → AffineMenu (A m))
    (f : ℕ → ℝ → ℝ)
    (chosen : (m : ℕ) → Ω m → A m)
    (K S : (m : ℕ) → Ω m → ℝ) {z : ℝ}
    (hUp : Request02NormalizationInput μ M f chosen K S z)
    (hK : ∀ m, ∀ᵐ ω ∂μ m, 0 ≤ K m ω)
    (hNoRoute : ∀ m, ∀ᵐ ω ∂μ m,
      K m ω = 0 → (M m).failure (chosen m ω) = 1) :
    ProbZero μ (fun m ω => S m ω / K m ω - 1) := by
  intro ε hε η hη
  have hCsmall : ∀ᶠ m in atTop, f m z < 1 / 2 :=
    hUp.scale_small.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [hCsmall,
    hUp.uniform_routed_acceptance (ε / 2) (by linarith),
    hUp.failure_small 1 (by norm_num) η hη] with m hmC hmR hmD
  apply lt_of_le_of_lt _ hmD
  apply measure_mono_ae
  filter_upwards [hK m, hNoRoute m, hmR] with ω hKω hNω hRω
  intro hbad
  by_cases hkpos : 0 < K m ω
  · have hg := hRω hkpos
    exact False.elim (not_lt_of_ge (by linarith : |S m ω / K m ω - 1| ≤ ε) hbad)
  · have hk0 : K m ω = 0 := le_antisymm (le_of_not_gt hkpos) hKω
    change 1 < |(M m).failure (chosen m ω) / f m z|
    rw [hNω hk0]
    have hCpos := hUp.scale_pos m
    rw [abs_of_pos (div_pos (by norm_num) hCpos)]
    apply (lt_div_iff₀ hCpos).2
    nlinarith

theorem normalized_bid_from_used_failure
    (μ : (m : ℕ) → Measure (Ω m))
    (M : (m : ℕ) → AffineMenu (A m))
    (f : ℕ → ℝ → ℝ)
    (V : (m : ℕ) → Ω m → ℝ)
    (chosen : (m : ℕ) → Ω m → A m)
    (K B S : (m : ℕ) → Ω m → ℝ)
    {ell z : ℝ} (hell : 0 ≤ ell) (hz : ell < z)
    (hE : ∀ m, IsEnvelope (M m) (f m))
    (hBest : ∀ m, ∀ᵐ ω ∂μ m,
      0 ≤ V m ω ∧ IsBestReply (M m) (V m ω) (chosen m ω))
    (hBands : PositiveLowerBands μ V ell)
    (hCompact : CompactContainment μ V ell)
    (hUp : Request02UsedFailure μ M f chosen z)
    (hAcceptance : ProbZero μ (fun m ω => S m ω / K m ω - 1))
    (hActual : ∀ m, ∀ᵐ ω ∂μ m,
      0 ≤ K m ω ∧ 0 ≤ B m ω ∧ 0 ≤ S m ω ∧ S m ω ≤ K m ω ∧
        (M m).payment (chosen m ω) = B m ω * S m ω) :
    ProbZero μ (fun m ω => K m ω * B m ω / f m z - 1) := by
  have hPoint : ∀ w : ℝ, ell < w →
      Tendsto (fun m => f m w / f m z) atTop (𝓝 1) :=
    fun w hw => pointwise_deficit_normalization μ M f V chosen
      hell hz hE hBest hBands hUp hw
  have hF := random_deficit_normalization μ V f hell
    (fun m => envelope_monotone (hE m)) hUp.scale_pos hPoint hCompact
  have hY := probZero_value_mul μ V
    (fun m ω => (M m).failure (chosen m ω) / f m z)
    hCompact hUp.failure_small
  apply probZero_bid_of_identity μ
    (fun m ω => K m ω * B m ω / f m z)
    (fun m ω => V m ω * ((M m).failure (chosen m ω) / f m z))
    (fun m ω => S m ω / K m ω)
    (fun m ω => f m (V m ω) / f m z)
    hF hY hAcceptance
  intro m
  filter_upwards [hBest m, hActual m] with ω hω hA
  have hC := hUp.scale_pos m
  have hratio : S m ω / K m ω ≤ 1 := by
    by_cases hk : K m ω = 0
    · simp [hk]
    · have hkpos : 0 < K m ω := lt_of_le_of_ne hA.1 (Ne.symm hk)
      exact (div_le_one hkpos).2 hA.2.2.2.1
  refine ⟨div_nonneg (mul_nonneg hA.1 hA.2.1) (le_of_lt hC),
    mul_nonneg hω.1
      (div_nonneg ((M m).failure_nonneg _) (le_of_lt hC)), hratio, ?_⟩
  apply payment_normalization_identity hA.2.2.1 hA.2.2.2.1 hC
  rw [bestReply_touches (hE m) hω.1 hω.2, hA.2.2.2.2]

end Probability

section Tiers

def TierGood {α : Type u} (n : ℕ) (δ : ℝ)
    (K : α → ℕ) (β : α → ℝ) (ω : α) : Prop :=
  0 < K ω ∧ K ω ≤ n ∧ |(K ω : ℝ) * β ω - 1| ≤ δ

theorem tier_separation {n k l : ℕ} {β γ δ : ℝ}
    (hk : 0 < k) (hkl : k < l) (hln : l ≤ n)
    (hδ0 : 0 ≤ δ) (hδn : δ ≤ 1 / (4 * (n : ℝ)))
    (hβ : |(k : ℝ) * β - 1| ≤ δ)
    (hγ : |(l : ℝ) * γ - 1| ≤ δ) :
    γ < β := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hlR : 0 < (l : ℝ) := by exact_mod_cast (lt_trans hk hkl)
  have hklR : (k : ℝ) < (l : ℝ) := by exact_mod_cast hkl
  have hlnR : (l : ℝ) ≤ (n : ℝ) := by exact_mod_cast hln
  have hnR : 0 < (n : ℝ) := lt_of_lt_of_le hlR hlnR
  have hgap : (k : ℝ) + 1 ≤ (l : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr hkl)
  have hsum : (k : ℝ) + (l : ℝ) ≤ 2 * (n : ℝ) := by linarith
  have hδN : δ * (4 * (n : ℝ)) ≤ 1 :=
    (le_div_iff₀ (by positivity : 0 < 4 * (n : ℝ))).mp hδn
  have hprod := mul_le_mul_of_nonneg_left hsum hδ0
  have hstrict : 0 < (l : ℝ) - (k : ℝ) - δ * ((k : ℝ) + (l : ℝ)) := by
    nlinarith
  have hβlow : 1 - δ ≤ (k : ℝ) * β := by
    have := (abs_le.mp hβ).1
    linarith
  have hγupper : (l : ℝ) * γ ≤ 1 + δ := by
    have := (abs_le.mp hγ).2
    linarith
  have hbscaled := mul_le_mul_of_nonneg_left hβlow (le_of_lt hlR)
  have hgscaled := mul_le_mul_of_nonneg_left hγupper (le_of_lt hkR)
  by_contra h
  have horder := mul_le_mul_of_nonneg_left (le_of_not_gt h)
    (mul_nonneg (le_of_lt hkR) (le_of_lt hlR))
  nlinarith

theorem higher_bid_prefix_bounds {α : Type u} [MeasurableSpace α]
    (μ : Measure α) (K : α → ℕ) (β : α → ℝ)
    {n k : ℕ} {δ x : ℝ}
    (hδ0 : 0 ≤ δ) (hδn : δ ≤ 1 / (4 * (n : ℝ)))
    (hk : 0 < k) (hkn : k ≤ n)
    (hx : |(k : ℝ) * x - 1| ≤ δ) :
    μ {ω | K ω < k} ≤
        μ {ω | x < β ω} + μ {ω | ¬ TierGood n δ K β ω} ∧
    μ {ω | x < β ω} ≤
        μ {ω | K ω ≤ k} + μ {ω | ¬ TierGood n δ K β ω} := by
  classical
  constructor
  · have hsub : {ω | K ω < k} ⊆
        {ω | x < β ω} ∪ {ω | ¬ TierGood n δ K β ω} := by
      intro ω hω
      by_cases hg : TierGood n δ K β ω
      · left
        exact tier_separation hg.1 hω hkn hδ0 hδn hg.2.2 hx
      · exact Or.inr hg
    exact (measure_mono hsub).trans (measure_union_le _ _)
  · have hsub : {ω | x < β ω} ⊆
        {ω | K ω ≤ k} ∪ {ω | ¬ TierGood n δ K β ω} := by
      intro ω hω
      by_cases hg : TierGood n δ K β ω
      · by_cases hclass : K ω ≤ k
        · exact Or.inl hclass
        · have hrev := tier_separation hk (lt_of_not_ge hclass)
            hg.2.1 hδ0 hδn hx hg.2.2
          exact False.elim ((not_lt_of_gt hrev) hω)
      · exact Or.inr hg
    exact (measure_mono hsub).trans (measure_union_le _ _)

theorem off_tier_prefix {α : Type u}
    (K : α → ℕ) (β : α → ℝ)
    {n k : ℕ} {δ x : ℝ}
    (hx0 : 0 ≤ x)
    (hlo : 1 + δ < x * ((k : ℝ) + 1))
    (hhi : x * (k : ℝ) < 1 - δ)
    {ω : α} (hg : TierGood n δ K β ω) :
    (x < β ω ↔ K ω ≤ k) := by
  have hKR : 0 < (K ω : ℝ) := by exact_mod_cast hg.1
  constructor
  · intro hxb
    by_contra hK
    have hKnat : k + 1 ≤ K ω := Nat.succ_le_iff.mpr (lt_of_not_ge hK)
    have hKreal : (k : ℝ) + 1 ≤ (K ω : ℝ) := by exact_mod_cast hKnat
    have hmul := mul_le_mul_of_nonneg_left hKreal hx0
    have hbid : (K ω : ℝ) * β ω ≤ 1 + δ := by
      have := (abs_le.mp hg.2.2).2
      linarith
    have horder := mul_lt_mul_of_pos_left hxb hKR
    nlinarith
  · intro hK
    have hKreal : (K ω : ℝ) ≤ (k : ℝ) := by exact_mod_cast hK
    have hmul := mul_le_mul_of_nonneg_left hKreal hx0
    have hbid : 1 - δ ≤ (K ω : ℝ) * β ω := by
      have := (abs_le.mp hg.2.2).1
      linarith
    have horder : (K ω : ℝ) * x < (K ω : ℝ) * β ω := by nlinarith
    exact (mul_lt_mul_iff_right₀ hKR).mp horder

theorem off_tier_symmetric_difference_subset {α : Type u}
    (K : α → ℕ) (β : α → ℝ)
    {n k : ℕ} {δ x : ℝ}
    (hx0 : 0 ≤ x)
    (hlo : 1 + δ < x * ((k : ℝ) + 1))
    (hhi : x * (k : ℝ) < 1 - δ) :
    {ω | (x < β ω ∧ ¬ K ω ≤ k) ∨ (K ω ≤ k ∧ ¬ x < β ω)}
      ⊆ {ω | ¬ TierGood n δ K β ω} := by
  intro ω hω hg
  have heq := off_tier_prefix K β hx0 hlo hhi hg
  rcases hω with hω | hω
  · exact hω.2 (heq.mp hω.1)
  · exact hω.2 (heq.mpr hω.1)

theorem charge_order_iff {a C b c : ℝ} (ha : 0 < a) (hC : 0 < C) :
    a * b / C < a * c / C ↔ b < c := by
  rw [div_lt_div_iff_of_pos_right hC, mul_lt_mul_iff_right₀ ha]

theorem exists_off_tier_cut {k : ℕ} {δ : ℝ}
    (hk : 0 < k) (hδ0 : 0 ≤ δ) (_hδ1 : δ < 1)
    (hgap : δ * (2 * (k : ℝ) + 1) < 1) :
    ∃ x : ℝ, 0 < x ∧ x < 1 / (k : ℝ) ∧
      1 + δ < x * ((k : ℝ) + 1) ∧
      x * (k : ℝ) < 1 - δ := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hkp : 0 < (k : ℝ) + 1 := by linarith
  let lo : ℝ := (1 + δ) / ((k : ℝ) + 1)
  let hi : ℝ := (1 - δ) / (k : ℝ)
  have hLoPos : 0 < lo := div_pos (by linarith) hkp
  have hLoHi : lo < hi := by
    dsimp [lo, hi]
    apply (div_lt_div_iff₀ hkp hkR).2
    nlinarith
  have hHiBound : hi ≤ 1 / (k : ℝ) := by
    dsimp [hi]
    exact (div_le_div_iff_of_pos_right hkR).2 (by linarith)
  refine ⟨(lo + hi) / 2, ?_, ?_, ?_, ?_⟩
  · linarith
  · linarith
  · apply (div_lt_iff₀ hkp).mp
    change lo < (lo + hi) / 2
    linarith
  · apply (lt_div_iff₀ hkR).mp
    change (lo + hi) / 2 < hi
    linarith

theorem eventually_off_tier_affordable
    (C : ℕ → ℝ) (hC : ∀ m, 0 < C m)
    (hLim : Tendsto C atTop (𝓝 0)) {x w : ℝ}
    (hx : 0 < x) (hw : 0 < w) :
    ∀ᶠ m in atTop, 0 < C m * x ∧ C m * x < w := by
  have hProd : Tendsto (fun m => C m * x) atTop (𝓝 0) := by
    simpa only [zero_mul] using hLim.mul_const x
  filter_upwards [hProd.eventually (eventually_lt_nhds hw)] with m hm
  exact ⟨mul_pos (hC m) hx, hm⟩

variable {Ω : ℕ → Type u} [∀ m, MeasurableSpace (Ω m)]

theorem tier_exceptional_mass_vanishes
    (μ : (m : ℕ) → Measure (Ω m))
    (K : (m : ℕ) → Ω m → ℕ) (β : (m : ℕ) → Ω m → ℝ)
    {n : ℕ} (hcap : ∀ m, ∀ᵐ ω ∂μ m, K m ω ≤ n)
    (hNorm : ProbZero μ (fun m ω => (K m ω : ℝ) * β m ω - 1))
    {δ : ℝ} (hδ0 : 0 < δ) (_hδ1 : δ < 1)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ m in atTop,
      μ m {ω | ¬ TierGood n δ (K m) (β m) ω} < ENNReal.ofReal η := by
  filter_upwards [hNorm δ hδ0 η hη] with m hm
  apply lt_of_le_of_lt _ hm
  apply measure_mono_ae
  filter_upwards [hcap m] with ω hω
  intro hbad
  by_contra hsmall
  have herr : |(K m ω : ℝ) * β m ω - 1| ≤ δ := le_of_not_gt hsmall
  have hk : 0 < K m ω := by
    by_contra hn
    have hk0 : K m ω = 0 := Nat.eq_zero_of_not_pos hn
    have : (1 : ℝ) ≤ δ := by simpa [hk0] using herr
    linarith
  exact hbad ⟨hk, hω, herr⟩

end Tiers
end FCAppendix.Ample.DownstreamNormalizationCore
