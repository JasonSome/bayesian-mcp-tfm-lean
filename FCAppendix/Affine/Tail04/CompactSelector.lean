import Mathlib

noncomputable section
namespace FCAppendix.Affine.Tail04.CompactSelector
open MeasureTheory Set Filter TopologicalSpace Metric Classical Topology

local instance : MeasurableSpace (List ℕ) := ⊤
local instance : MeasurableSingletonClass (List ℕ) := ⟨fun _ => trivial⟩

section MeasurableHelpers
variable {X C : Type*} [MeasurableSpace X] [MeasurableSpace C]
  [Countable C] [MeasurableSingletonClass C]

lemma measurableSet_countable_sections (P : X × C → Prop)
    (hP : ∀ c, MeasurableSet {x | P (x,c)}) :
    MeasurableSet {z | P z} := by
  have he : {z | P z} = ⋃ c : C,
      Prod.fst ⁻¹' {x | P (x,c)} ∩ Prod.snd ⁻¹' {c} := by
    ext z
    simp
  rw [he]
  exact MeasurableSet.iUnion fun c =>
    (measurable_fst (hP c)).inter (measurable_snd (measurableSet_singleton c))

lemma nat_find_eq_iff (P : ℕ → Prop) (hP : ∃ n, P n) (n : ℕ) :
    Nat.find hP=n ↔ P n ∧ ∀ i< n, ¬P i := by
  constructor
  · intro hn
    refine ⟨hn ▸ Nat.find_spec hP,?_⟩
    intro i hi hPi
    have hh := Nat.find_min' hP hPi
    omega
  · rintro ⟨hn,hlt⟩
    apply Nat.le_antisymm (Nat.find_min' hP hn)
    by_contra hh
    exact hlt (Nat.find hP) (by omega) (Nat.find_spec hP)

lemma measurable_nat_find (P : X → ℕ → Prop) (hP : ∀ x, ∃ n, P x n)
    (hmeas : ∀ n, MeasurableSet {x | P x n}) :
    Measurable (fun x => Nat.find (hP x)) := by
  apply measurable_to_countable'
  intro n
  have he : (fun x => Nat.find (hP x)) ⁻¹' {n} =
      {x | P x n} ∩ ⋂ i : ℕ, {x | i< n → ¬P x i} := by
    ext x
    simp only [mem_preimage,mem_singleton_iff,mem_inter_iff,mem_setOf_eq,mem_iInter]
    exact nat_find_eq_iff (P x) (hP x) n
  rw [he]
  apply (hmeas n).inter
  apply MeasurableSet.iInter
  intro i
  by_cases hi : i< n
  · have heq : {x | i< n → ¬P x i}={x | ¬P x i} := by
      ext x
      exact ⟨fun h => h hi, fun h _ => h⟩
    rw [heq]
    exact (hmeas i).compl
  · simp only [hi,false_implies,setOf_true]
    exact MeasurableSet.univ

end MeasurableHelpers

section MetricConstruction
variable {P K : Type*} [TopologicalSpace P] [MeasurableSpace P] [BorelSpace P]
  [MetricSpace K] [MeasurableSpace K] [BorelSpace K] [CompactSpace K]
  [Nonempty K]

def radius (n : ℕ) : ℝ := 1/((n:ℝ)+1)

lemma radius_pos (n : ℕ) : 0 < radius n := by unfold radius; positivity

lemma tendsto_radius : Tendsto radius atTop (𝓝 (0:ℝ)) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

def region (d : ℕ → K) : List ℕ → Set K
  | [] => univ
  | j::l => region d l ∩ closedBall (d j) (radius l.length)

omit [MeasurableSpace K] [BorelSpace K] [CompactSpace K] [Nonempty K] in
lemma isClosed_region (d : ℕ → K) (l : List ℕ) : IsClosed (region d l) := by
  induction l with
  | nil => exact isClosed_univ
  | cons j l ih => exact ih.inter isClosed_closedBall

def Good (G : Set (P × K)) (d : ℕ → K) (p : P) (l : List ℕ) : Prop :=
  ∃ k, (p,k) ∈ G ∧ k ∈ region d l

omit [MeasurableSpace P] [BorelSpace P] [MeasurableSpace K] [BorelSpace K] [Nonempty K] in
lemma isClosed_good (G : Set (P × K)) (hG : IsClosed G)
    (d : ℕ → K) (l : List ℕ) : IsClosed {p | Good G d p l} := by
  let S : Set (P × K) := G ∩ Prod.snd ⁻¹' region d l
  have hS : IsClosed S := hG.inter ((isClosed_region d l).preimage continuous_snd)
  have he : {p | Good G d p l} = Prod.fst '' S := by
    ext p
    constructor
    · rintro ⟨k,hk,hl⟩
      exact ⟨(p,k),⟨hk,hl⟩,rfl⟩
    · rintro ⟨⟨p',k⟩,⟨hk,hl⟩,heq⟩
      change p'=p at heq
      subst p'
      exact ⟨k,hk,hl⟩
  rw [he]
  exact isClosedMap_fst_of_compactSpace S hS

omit [TopologicalSpace P] [MeasurableSpace P] [BorelSpace P]
  [MeasurableSpace K] [BorelSpace K] [CompactSpace K] [Nonempty K] in
lemma good_child_exists (G : Set (P × K)) (d : ℕ → K) (hd : DenseRange d)
    (p : P) (l : List ℕ) (hl : Good G d p l) :
    ∃ j, Good G d p (j::l) := by
  obtain ⟨k,hk,hlk⟩ := hl
  have hcover := (Metric.denseRange_iff.mp hd) k (radius l.length) (radius_pos _)
  obtain ⟨j,hj⟩ := hcover
  exact ⟨j,k,hk,hlk,le_of_lt hj⟩

omit [TopologicalSpace P] [MeasurableSpace P] [BorelSpace P] [MeasurableSpace K] [BorelSpace K] [CompactSpace K] [Nonempty K] in
lemma next_exists (G : Set (P × K)) (d : ℕ → K) (hd : DenseRange d)
    (z : P × List ℕ) : ∃ j, ¬Good G d z.1 z.2 ∨ Good G d z.1 (j::z.2) := by
  by_cases hz : Good G d z.1 z.2
  · obtain ⟨j,hj⟩ := good_child_exists G d hd z.1 z.2 hz
    exact ⟨j,Or.inr hj⟩
  · exact ⟨0,Or.inl hz⟩

def next (G : Set (P × K)) (d : ℕ → K) (hd : DenseRange d)
    (z : P × List ℕ) : ℕ :=
  @Nat.find (fun j => ¬Good G d z.1 z.2 ∨ Good G d z.1 (j::z.2))
    (fun _ => Classical.propDecidable _) (next_exists G d hd z)

omit [TopologicalSpace P] [MeasurableSpace P] [BorelSpace P] [MeasurableSpace K] [BorelSpace K] [CompactSpace K] [Nonempty K] in
lemma next_good (G : Set (P × K)) (d : ℕ → K) (hd : DenseRange d)
    (p : P) (l : List ℕ) (hl : Good G d p l) :
    Good G d p (next G d hd (p,l)::l) := by
  have hs := @Nat.find_spec
    (fun j => ¬Good G d p l ∨ Good G d p (j::l))
    (fun _ => Classical.propDecidable _) (next_exists G d hd (p,l))
  exact hs.resolve_left (not_not.mpr hl)

omit [MeasurableSpace K] [BorelSpace K] [Nonempty K] in
lemma measurable_next (G : Set (P × K)) (hG : IsClosed G)
    (d : ℕ → K) (hd : DenseRange d) : Measurable (next G d hd) := by
  unfold next
  apply measurable_nat_find
  intro j
  apply measurableSet_countable_sections
  intro l
  exact ((isClosed_good G hG d l).measurableSet.compl).union
    (isClosed_good G hG d (j::l)).measurableSet

def history (G : Set (P × K)) (d : ℕ → K) (hd : DenseRange d) : ℕ → P → List ℕ
  | 0,_ => []
  | n+1,p => next G d hd (p,history G d hd n p)::history G d hd n p

omit [TopologicalSpace P] [MeasurableSpace P] [BorelSpace P] [MeasurableSpace K] [BorelSpace K] [CompactSpace K] [Nonempty K] in
lemma history_length (G : Set (P × K)) (d : ℕ → K) (hd : DenseRange d)
    (n : ℕ) (p : P) : (history G d hd n p).length=n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [history,List.length_cons,ih]

omit [TopologicalSpace P] [MeasurableSpace P] [BorelSpace P] [MeasurableSpace K] [BorelSpace K] [CompactSpace K] [Nonempty K] in
lemma history_good (G : Set (P × K)) (hne : ∀ p, ∃ k, (p,k) ∈ G)
    (d : ℕ → K) (hd : DenseRange d) (n : ℕ) (p : P) :
    Good G d p (history G d hd n p) := by
  induction n with
  | zero => obtain ⟨k,hk⟩ := hne p; exact ⟨k,hk,mem_univ k⟩
  | succ n ih => exact next_good G d hd p _ ih

omit [MeasurableSpace K] [BorelSpace K] [Nonempty K] in
lemma measurable_history (G : Set (P × K)) (hG : IsClosed G)
    (d : ℕ → K) (hd : DenseRange d) (n : ℕ) :
    Measurable (history G d hd n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    exact (measurable_of_countable (fun z : ℕ × List ℕ => z.1::z.2)).comp
      (((measurable_next G hG d hd).comp (measurable_id.prodMk ih)).prodMk ih)

def fiberStage (G : Set (P × K)) (d : ℕ → K) (hd : DenseRange d)
    (p : P) (n : ℕ) : Set K :=
  {k | (p,k) ∈ G} ∩ region d (history G d hd n p)

omit [MeasurableSpace P] [BorelSpace P] [MeasurableSpace K] [BorelSpace K] [CompactSpace K] [Nonempty K] in
lemma isClosed_fiberStage (G : Set (P × K)) (hG : IsClosed G)
    (d : ℕ → K) (hd : DenseRange d) (p : P) (n : ℕ) :
    IsClosed (fiberStage G d hd p n) :=
  (hG.preimage (continuous_const.prodMk continuous_id)).inter (isClosed_region _ _)

omit [TopologicalSpace P] [MeasurableSpace P] [BorelSpace P] [MeasurableSpace K] [BorelSpace K] [CompactSpace K] [Nonempty K] in
lemma fiberStage_succ_subset (G : Set (P × K)) (d : ℕ → K) (hd : DenseRange d)
    (p : P) (n : ℕ) : fiberStage G d hd p (n+1) ⊆ fiberStage G d hd p n := by
  intro k hk
  exact ⟨hk.1,hk.2.1⟩

omit [MeasurableSpace P] [BorelSpace P] [MeasurableSpace K] [BorelSpace K] [Nonempty K] in
lemma stages_nonempty (G : Set (P × K)) (hG : IsClosed G)
    (hne : ∀ p, ∃ k, (p,k) ∈ G) (d : ℕ → K) (hd : DenseRange d) (p : P) :
    (⋂ n, fiberStage G d hd p n).Nonempty := by
  apply IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
  · exact fiberStage_succ_subset G d hd p
  · intro n
    exact history_good G hne d hd n p
  · exact (isClosed_fiberStage G hG d hd p 0).isCompact
  · exact isClosed_fiberStage G hG d hd p

def selected (G : Set (P × K)) (hG : IsClosed G)
    (hne : ∀ p, ∃ k, (p,k) ∈ G) (d : ℕ → K) (hd : DenseRange d) (p : P) : K :=
  (stages_nonempty G hG hne d hd p).choose

omit [MeasurableSpace P] [BorelSpace P] [MeasurableSpace K] [BorelSpace K] [Nonempty K] in
lemma selected_stage (G : Set (P × K)) (hG : IsClosed G)
    (hne : ∀ p, ∃ k, (p,k) ∈ G) (d : ℕ → K) (hd : DenseRange d)
    (p : P) (n : ℕ) : selected G hG hne d hd p ∈ fiberStage G d hd p n :=
  mem_iInter.mp (stages_nonempty G hG hne d hd p).choose_spec n

omit [MeasurableSpace P] [BorelSpace P] [MeasurableSpace K] [BorelSpace K] [Nonempty K] in
lemma selected_mem (G : Set (P × K)) (hG : IsClosed G)
    (hne : ∀ p, ∃ k, (p,k) ∈ G) (d : ℕ → K) (hd : DenseRange d) (p : P) :
    (p,selected G hG hne d hd p) ∈ G := (selected_stage G hG hne d hd p 0).1

def center (G : Set (P × K)) (d : ℕ → K) (hd : DenseRange d) (n : ℕ) (p : P) : K :=
  d (next G d hd (p,history G d hd n p))

omit [BorelSpace K] [Nonempty K] in
lemma measurable_center (G : Set (P × K)) (hG : IsClosed G)
    (d : ℕ → K) (hd : DenseRange d) (n : ℕ) : Measurable (center G d hd n) :=
  (measurable_of_countable d).comp ((measurable_next G hG d hd).comp
    (measurable_id.prodMk (measurable_history G hG d hd n)))

omit [MeasurableSpace P] [BorelSpace P] [MeasurableSpace K] [BorelSpace K] [Nonempty K] in
lemma center_dist_selected_le (G : Set (P × K)) (hG : IsClosed G)
    (hne : ∀ p, ∃ k, (p,k) ∈ G) (d : ℕ → K) (hd : DenseRange d)
    (p : P) (n : ℕ) :
    dist (center G d hd n p) (selected G hG hne d hd p) ≤ radius n := by
  have hh := (selected_stage G hG hne d hd p (n+1)).2.2
  simpa only [history,region,mem_closedBall,history_length,center,dist_comm] using hh

omit [MeasurableSpace P] [BorelSpace P] [MeasurableSpace K] [BorelSpace K] [Nonempty K] in
lemma center_tendsto (G : Set (P × K)) (hG : IsClosed G)
    (hne : ∀ p, ∃ k, (p,k) ∈ G) (d : ℕ → K) (hd : DenseRange d) (p : P) :
    Tendsto (fun n => center G d hd n p) atTop (𝓝 (selected G hG hne d hd p)) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N,hN⟩ := eventually_atTop.mp (tendsto_radius.eventually (gt_mem_nhds hε))
  exact ⟨N,fun n hn => (center_dist_selected_le G hG hne d hd p n).trans_lt (hN n hn)⟩

omit [Nonempty K] in
lemma measurable_selected (G : Set (P × K)) (hG : IsClosed G)
    (hne : ∀ p, ∃ k, (p,k) ∈ G) (d : ℕ → K) (hd : DenseRange d) :
    Measurable (selected G hG hne d hd) :=
  measurable_of_tendsto_metrizable (measurable_center G hG d hd)
    (tendsto_pi_nhds.mpr (center_tendsto G hG hne d hd))

end MetricConstruction

theorem exists_measurable_selector {P K : Type*}
    [TopologicalSpace P] [MeasurableSpace P] [BorelSpace P]
    [TopologicalSpace K] [MeasurableSpace K] [BorelSpace K]
    [MetrizableSpace K] [CompactSpace K] [Nonempty K]
    (G : Set (P × K)) (hG : IsClosed G) (hne : ∀ p, ∃ k, (p,k) ∈ G) :
    ∃ f : P → K, Measurable f ∧ ∀ p, (p,f p) ∈ G := by
  letI : MetricSpace K := TopologicalSpace.metrizableSpaceMetric K
  obtain ⟨d,hd⟩ := exists_dense_seq K
  exact ⟨selected G hG hne d hd,measurable_selected G hG hne d hd,
    selected_mem G hG hne d hd⟩

end FCAppendix.Affine.Tail04.CompactSelector
