import FCAppendix.Affine.Tail04.NativeFocalReceipts
import FCAppendix.Affine.Tail04.NativeRawFallback
import FCAppendix.Affine.Tail04.NativeFullReceipts

noncomputable section
namespace FCAppendix.Affine.Tail04.NativeLocalPolicy.Data
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open scoped BigOperators

variable {m c : ℕ} (D : NativeLocalPolicy.Data m c)

local instance completedPolicyOptionDiscrete : DiscreteMeasurableSpace (Option (Fin m)) :=
  ⟨fun s=>by
    change MeasurableSet ((some : Fin m→Option (Fin m)) ⁻¹' s)
    exact MeasurableSet.of_discrete⟩

def firstOff (S : Finset (Fin m)) : Option (Fin m) :=
  if h : S.Nonempty then some (S.min' h) else none

def offCandidate (L : LocalList m) : Option (Fin m) := firstOff (D.offCommon L)

lemma measurable_offCandidate : Measurable D.offCandidate :=
  (measurable_of_countable firstOff).comp D.measurable_offCommon

lemma firstOff_none (S : Finset (Fin m)) : firstOff S=none ↔ S=∅ := by
  by_cases h : S.Nonempty
  · simp [firstOff,h,Finset.Nonempty.ne_empty h]
  · simp [firstOff,Finset.not_nonempty_iff_eq_empty.mp h]

lemma firstOff_singleton (i : Fin m) : firstOff {i}=some i := by
  simp [firstOff]

lemma offCommon_eq_empty_iff (L : LocalList m) : D.offCommon L=∅ ↔
    ∀ i,D.E.localTag (L i)=1 → entryBid (L i)∈Icc (1:ℝ) D.E.U := by
  simp only [offCommon,Finset.filter_eq_empty_iff,Finset.mem_univ,true_implies,
    not_and,not_not]

def completedPolicy (j : Fin 2) : LocalPolicy m c NativeLocalPolicy.Seed :=
  fun L u => match D.offCandidate L with
  | none => D.policy j L u
  | some i => if D.UseFocal j i L then D.focalPolicy j i L u else D.rawFallback j L u

lemma completedPolicy_measurable (j : Fin 2) :
    Measurable (fun z : LocalList m×NativeLocalPolicy.Seed => (D.completedPolicy j z.1 z.2).val) := by
  have hf : Measurable (fun z : Option (Fin m) × (LocalList m×NativeLocalPolicy.Seed) =>
      match z.1 with
      | none => (D.policy j z.2.1 z.2.2).val
      | some i => if D.UseFocal j i z.2.1 then (D.focalPolicy j i z.2.1 z.2.2).val
          else (D.rawFallback j z.2.1 z.2.2).val) := by
    apply measurable_from_prod_countable_right
    intro k
    cases k with
    | none => exact D.policy_measurable j
    | some i =>
      exact Measurable.ite ((D.measurableSet_useFocal j i).preimage measurable_fst)
        (D.focalPolicy_measurable j i) (D.rawFallback_measurable j)
  convert! hf.comp ((D.measurable_offCandidate.comp measurable_fst).prodMk measurable_id) using 1
  funext z
  dsimp only [Function.comp_def,id]
  cases he : D.offCandidate z.1 with
  | none => simp only [completedPolicy,he]
  | some i =>
    by_cases hu : D.UseFocal j i z.1 <;> simp [completedPolicy,he,hu]

lemma completed_on_menu (j : Fin 2) (L : LocalList m) (h : D.offCommon L=∅)
    (u : NativeLocalPolicy.Seed) : D.completedPolicy j L u=D.policy j L u := by
  have hc : D.offCandidate L=none := (firstOff_none _).mpr h
  simp [completedPolicy,hc]

lemma completed_focal (j : Fin 2) (i : Fin m) (L : LocalList m)
    (h : D.UseFocal j i L) (u : NativeLocalPolicy.Seed) :
    D.completedPolicy j L u=D.focalPolicy j i L u := by
  have hc : D.offCandidate L=some i := by simp [offCandidate,h.1,firstOff_singleton]
  simp [completedPolicy,hc,h]

lemma completed_fallback (j : Fin 2) (L : LocalList m) (h : D.offCommon L≠∅)
    (hf : ∀ i,¬D.UseFocal j i L) (u : NativeLocalPolicy.Seed) :
    D.completedPolicy j L u=D.rawFallback j L u := by
  have hc : D.offCandidate L≠none := fun he => h ((firstOff_none _).mp he)
  cases he : D.offCandidate L with
  | none => exact (hc he).elim
  | some i => simp [completedPolicy,he,hf i]

def completedNumericalReceipt (j : Fin 2) (L : LocalList m) : Fin m → ℝ :=
  match D.offCandidate L with
  | none => D.numericalReceipt j L
  | some i => if D.UseFocal j i L then D.focalNumericalReceipt j i L else D.rawNumericalReceipt j L

lemma completedNumericalReceipt_on_menu (j : Fin 2) (L : LocalList m)
    (h : D.offCommon L=∅) : D.completedNumericalReceipt j L=D.numericalReceipt j L := by
  have hc : D.offCandidate L=none := (firstOff_none _).mpr h
  simp [completedNumericalReceipt,hc]

theorem completed_numerical_optimal (hlow : D.E.d<1-D.ξ)
    (j : Fin 2) (L : LocalList m) (hL : NonnegativeList L) (u : NativeLocalPolicy.Seed) :
    Finite.Optimal c (D.completedNumericalReceipt j L) ((D.completedPolicy j L u).val) := by
  cases he : D.offCandidate L with
  | none =>
    simpa only [completedPolicy,completedNumericalReceipt,he] using D.numerical_optimal hlow j L hL u
  | some i =>
    by_cases hu : D.UseFocal j i L
    · simpa only [completedPolicy,completedNumericalReceipt,he,if_pos hu] using
        D.focalPolicy_numerical_optimal hlow j i L hL hu u
    · simpa only [completedPolicy,completedNumericalReceipt,he,if_neg hu] using
        D.rawFallback_numerical_optimal j L hL u

end FCAppendix.Affine.Tail04.NativeLocalPolicy.Data
