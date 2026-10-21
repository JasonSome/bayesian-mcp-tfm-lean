import FCAppendix.Affine.Hybrid.SupportSampler

noncomputable section
namespace FCAppendix.Affine.UniformFinite.ExtensionalSampler
open MeasureTheory Set Classical
open scoped BigOperators

variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]
  [MeasurableSpace Ω] [MeasurableSingletonClass Ω] [StandardBorelSpace Ω]

def Vector (Ω : Type*) [Fintype Ω] :=
  {p : Ω→ℝ // (∀a,0≤ p a) ∧ ∑a,p a=1}

instance : MeasurableSpace (Vector Ω) := inferInstanceAs
  (MeasurableSpace {p : Ω→ℝ // (∀a,0≤ p a) ∧ ∑a,p a=1})

def encode (P : FiniteLaw Ω) : Vector Ω := ⟨P.mass,P.nonneg,P.total⟩

def decode (p : Vector Ω) : FiniteLaw Ω := ⟨p.val,p.property.1,p.property.2⟩

omit [Nonempty Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω] [StandardBorelSpace Ω] in
@[simp] theorem decode_encode (P : FiniteLaw Ω) : decode (encode P)=P := by
  apply FiniteLaw.ext
  intro a
  rfl

private theorem exists_sampler : ∃f : Vector Ω→ unitInterval→Ω,
    Measurable (Function.uncurry f) ∧
    (∀p u,0<(decode p).mass (f p u)) ∧
    ∀p,volume.map (f p)=FiniteLaw.probabilityMeasure (decode p) :=
  Hybrid.exists_support_sampler decode (fun a=>
    (measurable_pi_apply a).comp measurable_subtype_coe)

private def vectorSample : Vector Ω→ unitInterval→Ω := exists_sampler.choose

def sample (P : FiniteLaw Ω) (u : unitInterval) : Ω := vectorSample (encode P) u

theorem support (P : FiniteLaw Ω) (u : unitInterval) :
    0< P.mass (sample P u) := by
  simpa only [sample,vectorSample,decode_encode] using
    exists_sampler.choose_spec.2.1 (encode P) u

theorem law (P : FiniteLaw Ω) :
    volume.map (sample P)=FiniteLaw.probabilityMeasure P := by
  have h := exists_sampler.choose_spec.2.2 (encode P)
  rw [decode_encode] at h
  exact h

theorem measurable_family {X : Type*} [MeasurableSpace X]
    (P : X→ FiniteLaw Ω) (hP : ∀a,Measurable (fun x=>(P x).mass a)) :
    Measurable (fun x : X×unitInterval=> sample (P x.1) x.2) := by
  have he : Measurable (fun x : X=> encode (P x)) :=
    Measurable.subtype_mk (measurable_pi_lambda _ hP)
  exact exists_sampler.choose_spec.1.comp
    ((he.comp measurable_fst).prodMk measurable_snd)

theorem congr {P Q : FiniteLaw Ω} (h : P=Q) (u : unitInterval) :
    sample P u=sample Q u := congrArg (fun P=> sample P u) h

theorem dirac (a : Ω) (u : unitInterval) : sample (FiniteLaw.dirac a) u=a := by
  have hp:=support (FiniteLaw.dirac a) u
  by_contra hn
  change 0 < if sample (FiniteLaw.dirac a) u = a then (1 : ℝ) else 0 at hp
  simp only [if_neg hn, lt_self_iff_false] at hp

end FCAppendix.Affine.UniformFinite.ExtensionalSampler
