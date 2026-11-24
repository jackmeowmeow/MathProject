import MathProject.Basic

/-!
# Ultraproducts with partial representatives and Łoś's Theorem

This file follows Mathlib's `Mathlib/ModelTheory/Ultraproducts.lean` step by step, with
`Filter.Product` replaced by `Product.PartialProduct`: representatives are sections defined
on a set in the ultrafilter instead of functions defined at every index.

Mathlib needs every structure `M a` to be nonempty. With partial representatives this
assumption is not needed.

## Main Definitions

- `FirstOrder.Language.PartialUltraproduct.structure` is the ultraproduct structure on
  `Product.PartialProduct`.

## Main Results

- Łoś's Theorem: `FirstOrder.Language.PartialUltraproduct.sentence_realize`. A partial
  ultraproduct models a sentence `φ` if and only if the set of structures in the product that
  model `φ` is in the ultrafilter. No structure `M a` needs to be nonempty.

## Tags

ultraproduct, Los's theorem
-/

universe u v

variable {α : Type*} (M : α → Type*) (u : Ultrafilter α)

open FirstOrder Filter Set Product

namespace FirstOrder

namespace Language

open Structure

variable {L : FirstOrder.Language.{u, v}} [∀ a, L.Structure (M a)]

namespace PartialUltraproduct

variable {M} {u}

/-- The common domain of finitely many sections: a finite intersection of sets in `u`. -/
def commonDomain {ι : Type*} (x : ι → Section (u : Filter α) M) : Set α :=
  ⋂ i, (x i).domain

theorem commonDomain_mem {ι : Type*} [Finite ι] (x : ι → Section (u : Filter α) M) :
    commonDomain x ∈ (u : Filter α) :=
  iInter_mem.2 fun i ↦ (x i).large

/-- The values of finitely many sections at an index of their common domain. -/
def valuesAt {ι : Type*} (x : ι → Section (u : Filter α) M) {a : α}
    (h : a ∈ commonDomain x) : ι → M a :=
  fun i ↦ (x i).value ⟨a, mem_iInter.1 h i⟩

variable (M u)

/-- Sections carry a first-order structure, computed index by index on the common domain of
the arguments, and it respects the equivalence of sections. -/
instance setoidPrestructure : L.Prestructure (partialProductSetoid (u : Filter α) M) where
  toStructure :=
    { funMap := fun f x ↦ ⟨commonDomain x, commonDomain_mem x,
        fun a ↦ funMap f (valuesAt x a.2)⟩
      RelMap := fun r x ↦ ∀ᶠ a in (u : Filter α), ∀ h : a ∈ commonDomain x,
        RelMap r (valuesAt x h) }
  fun_equiv := by
    intro n f x y xy
    show ∀ᶠ a in (u : Filter α), _
    filter_upwards [eventually_all.2 xy] with a ha
    intro h₁ h₂
    show funMap f (valuesAt x h₁) = funMap f (valuesAt y h₂)
    congr 1
    funext i
    exact ha i _ _
  rel_equiv := by
    intro n r x y xy
    apply propext
    constructor
    · intro hx
      filter_upwards [hx, eventually_all.2 xy, commonDomain_mem x] with a hxa ha hdom
      intro h
      have e : valuesAt x hdom = valuesAt y h := funext fun i ↦ ha i _ _
      rw [← e]
      exact hxa hdom
    · intro hy
      filter_upwards [hy, eventually_all.2 xy, commonDomain_mem y] with a hya ha hdom
      intro h
      have e : valuesAt x h = valuesAt y hdom := funext fun i ↦ ha i _ _
      rw [e]
      exact hya hdom

variable {M} {u}

instance «structure» : L.Structure (PartialProduct (u : Filter α) M) :=
  inferInstanceAs <| L.Structure (Quotient (partialProductSetoid (u : Filter α) M))

/-- The equivalence of sections, as an instance so that `⟦s⟧` denotes the class of `s`. -/
local instance sectionSetoid : Setoid (Section (u : Filter α) M) :=
  partialProductSetoid (u : Filter α) M

/-- The structure on sections, used to compute realizations before taking classes. -/
local instance sectionStructure : L.Structure (Section (u : Filter α) M) :=
  (setoidPrestructure M u).toStructure

theorem funMap_cast {n : ℕ} (f : L.Functions n) (x : Fin n → Section (u : Filter α) M) :
    (funMap f fun i ↦ (⟦x i⟧ : PartialProduct (u : Filter α) M)) =
      (⟦⟨commonDomain x, commonDomain_mem x, fun a ↦ funMap f (valuesAt x a.2)⟩⟧ :
        PartialProduct (u : Filter α) M) := by
  apply funMap_quotient_mk'

/-- Where it is defined, the realization of a term in sections is computed index by index. -/
theorem term_realize_value {β : Type*} (x : β → Section (u : Filter α) M) (t : L.Term β)
    {a : α} (h₁ : a ∈ (t.realize x).domain) (h₂ : a ∈ commonDomain x) :
    (t.realize x).value ⟨a, h₁⟩ = t.realize (valuesAt x h₂) := by
  induction t with
  | var => rfl
  | func f ts ih =>
    show funMap f (valuesAt (fun i ↦ (ts i).realize x) h₁) = funMap f fun i ↦ (ts i).realize _
    congr 1
    funext i
    exact ih i _

theorem term_realize_cast {β : Type*} [Finite β] (x : β → Section (u : Filter α) M)
    (t : L.Term β) :
    (t.realize fun i ↦ (⟦x i⟧ : PartialProduct (u : Filter α) M)) =
      (⟦⟨commonDomain x, commonDomain_mem x, fun a ↦ t.realize (valuesAt x a.2)⟩⟧ :
        PartialProduct (u : Filter α) M) := by
  refine (Term.realize_quotient_mk' (partialProductSetoid (u : Filter α) M) t x).trans ?_
  apply Quotient.sound
  show ∀ᶠ a in (u : Filter α), _
  exact Eventually.of_forall fun a h₁ h₂ ↦ term_realize_value x t h₁ h₂

/-! ### Bookkeeping: joining two lists of sections

With functions defined at every index, as in Mathlib, these four facts hold by definition.
A section has a value only at the indices of its domain. So when the proof joins two lists
of sections, it must check that the common domain of the joined list is the intersection of
the two common domains, and that the joined list has the same values as its two parts. -/

theorem mem_commonDomain_sum {β : Type*} {n : ℕ} (x : β → Section (u : Filter α) M)
    (v : Fin n → Section (u : Filter α) M) {a : α} :
    a ∈ commonDomain (Sum.elim x v) ↔ a ∈ commonDomain x ∧ a ∈ commonDomain v := by
  simp only [commonDomain, mem_iInter, Sum.forall, Sum.elim_inl, Sum.elim_inr]

theorem valuesAt_sum {β : Type*} {n : ℕ} (x : β → Section (u : Filter α) M)
    (v : Fin n → Section (u : Filter α) M) {a : α} (h : a ∈ commonDomain (Sum.elim x v))
    (hx : a ∈ commonDomain x) (hv : a ∈ commonDomain v) :
    valuesAt (Sum.elim x v) h = Sum.elim (valuesAt x hx) (valuesAt v hv) := by
  funext j
  cases j <;> rfl

theorem mem_commonDomain_snoc {n : ℕ} (v : Fin n → Section (u : Filter α) M)
    (m : Section (u : Filter α) M) {a : α} :
    a ∈ commonDomain (Fin.snoc v m : Fin (n + 1) → Section (u : Filter α) M) ↔
      a ∈ commonDomain v ∧ a ∈ m.domain := by
  simp only [commonDomain, mem_iInter, Fin.forall_fin_succ', Fin.snoc_castSucc, Fin.snoc_last]

theorem valuesAt_snoc {n : ℕ} (v : Fin n → Section (u : Filter α) M)
    (m : Section (u : Filter α) M) {a : α}
    (h : a ∈ commonDomain (Fin.snoc v m : Fin (n + 1) → Section (u : Filter α) M))
    (hv : a ∈ commonDomain v) (hm : a ∈ m.domain) :
    valuesAt (Fin.snoc v m : Fin (n + 1) → Section (u : Filter α) M) h =
      Fin.snoc (valuesAt v hv) (m.value ⟨a, hm⟩) := by
  -- equal sections have equal values
  have key : ∀ s t : Section (u : Filter α) M, s = t → ∀ p q, s.value ⟨a, p⟩ = t.value ⟨a, q⟩ := by
    rintro s t rfl p q
    rfl
  funext i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · rw [Fin.snoc_last]
    exact key _ m (by simp) _ _
  · rw [Fin.snoc_castSucc]
    exact key _ (v j) (by simp) _ _

/-! ### Łoś's theorem for bounded formulas -/

theorem boundedFormula_realize_cast {β : Type*} [Finite β] {n : ℕ}
    (φ : L.BoundedFormula β n) (x : β → Section (u : Filter α) M)
    (v : Fin n → Section (u : Filter α) M) :
    (φ.Realize (fun i : β ↦ (⟦x i⟧ : PartialProduct (u : Filter α) M))
        (fun i ↦ (⟦v i⟧ : PartialProduct (u : Filter α) M))) ↔
      ∀ᶠ a : α in u, ∀ (hx : a ∈ commonDomain x) (hv : a ∈ commonDomain v),
        φ.Realize (valuesAt x hx) (valuesAt v hv) := by
  induction φ with
  | falsum =>
    simp only [BoundedFormula.Realize, false_iff]
    intro h
    have hx : ∀ᶠ a in (u : Filter α), a ∈ commonDomain x := commonDomain_mem x
    have hv : ∀ᶠ a in (u : Filter α), a ∈ commonDomain v := commonDomain_mem v
    obtain ⟨a, ha, hx, hv⟩ := (h.and (hx.and hv)).exists
    exact ha hx hv
  | @equal k t₁ t₂ =>
    have hs : (Sum.elim (fun i ↦ (⟦x i⟧ : PartialProduct (u : Filter α) M)) fun i ↦ ⟦v i⟧) =
        fun j ↦ ⟦Sum.elim x v j⟧ := funext fun j ↦ by cases j <;> rfl
    simp only [BoundedFormula.Realize]
    rw [hs, term_realize_cast, term_realize_cast, Quotient.eq]
    show (∀ᶠ a in (u : Filter α), ∀ h₁ h₂, t₁.realize (valuesAt (Sum.elim x v) h₁) =
      t₂.realize (valuesAt (Sum.elim x v) h₂)) ↔ _
    refine eventually_congr (Eventually.of_forall fun a ↦ ⟨fun H hx hv ↦ ?_, fun H h₁ h₂ ↦ ?_⟩)
    · have h := (mem_commonDomain_sum x v).2 ⟨hx, hv⟩
      have := H h h
      rwa [valuesAt_sum x v h hx hv] at this
    · obtain ⟨hx, hv⟩ := (mem_commonDomain_sum x v).1 h₁
      rw [valuesAt_sum x v h₁ hx hv]
      exact H hx hv
  | @rel k l R ts =>
    have hs : (Sum.elim (fun i ↦ (⟦x i⟧ : PartialProduct (u : Filter α) M)) fun i ↦ ⟦v i⟧) =
        fun j ↦ ⟦Sum.elim x v j⟧ := funext fun j ↦ by cases j <;> rfl
    simp only [BoundedFormula.Realize]
    rw [hs]
    have ht : (fun i ↦ (ts i).realize fun j ↦
        (⟦Sum.elim x v j⟧ : PartialProduct (u : Filter α) M)) =
        fun i ↦ ⟦⟨commonDomain (Sum.elim x v), commonDomain_mem (Sum.elim x v),
          fun a ↦ (ts i).realize (valuesAt (Sum.elim x v) a.2)⟩⟧ :=
      funext fun i ↦ term_realize_cast (Sum.elim x v) (ts i)
    rw [ht, relMap_quotient_mk' (partialProductSetoid (u : Filter α) M)]
    show (∀ᶠ a in (u : Filter α), ∀ h, RelMap R fun i ↦ (ts i).realize
      (valuesAt (Sum.elim x v) (mem_iInter.1 h i))) ↔ _
    constructor
    · intro H
      filter_upwards [H, commonDomain_mem (Sum.elim x v)] with a ha hy hx hv
      have := ha (mem_iInter.2 fun _ ↦ hy)
      simp only [valuesAt_sum x v _ hx hv] at this
      exact this
    · intro H
      filter_upwards [H, commonDomain_mem (Sum.elim x v)] with a ha hy h
      obtain ⟨hx, hv⟩ := (mem_commonDomain_sum x v).1 hy
      simp only [valuesAt_sum x v _ hx hv]
      exact ha hx hv
  | imp φ ψ ihφ ihψ =>
    simp only [BoundedFormula.Realize, ihφ, ihψ]
    rw [← Ultrafilter.eventually_imp]
    refine eventually_congr ?_
    filter_upwards [commonDomain_mem x, commonDomain_mem v] with a hx hv
    exact ⟨fun H hx' hv' h ↦ H (fun _ _ ↦ h) hx' hv',
      fun H h₁ hx' hv' ↦ H hx' hv' (h₁ hx' hv')⟩
  | @all k φ ih =>
    simp only [BoundedFormula.Realize]
    apply Iff.trans (b := ∀ m : Section (u : Filter α) M,
      φ.Realize (fun i : β ↦ (⟦x i⟧ : PartialProduct (u : Filter α) M))
        (Fin.snoc (fun i ↦ (⟦v i⟧ : PartialProduct (u : Filter α) M))
          (⟦m⟧ : PartialProduct (u : Filter α) M)))
    · exact Quotient.forall
    have hsnoc : ∀ m : Section (u : Filter α) M,
        (Fin.snoc (fun i ↦ (⟦v i⟧ : PartialProduct (u : Filter α) M)) ⟦m⟧ :
          Fin (k + 1) → PartialProduct (u : Filter α) M) =
        fun i ↦ ⟦(Fin.snoc v m : Fin (k + 1) → Section (u : Filter α) M) i⟧ := by
      intro m
      funext i
      refine Fin.lastCases ?_ (fun j ↦ ?_) i
      · exact (Fin.snoc_last (α := fun _ ↦ PartialProduct (u : Filter α) M) _ _).trans
          (congrArg _ (Fin.snoc_last (α := fun _ ↦ Section (u : Filter α) M) _ _).symm)
      · exact (Fin.snoc_castSucc (α := fun _ ↦ PartialProduct (u : Filter α) M) ..).trans
          (congrArg _ (Fin.snoc_castSucc (α := fun _ ↦ Section (u : Filter α) M) ..).symm)
    refine (forall_congr' fun m ↦
      (iff_of_eq (congrArg (φ.Realize _) (hsnoc m))).trans (ih _)).trans ?_
    constructor
    · intro h
      by_contra hne
      -- T: the indices where the formula fails for some element of `M a`
      have hT : {a | ∃ (hx : a ∈ commonDomain x) (hv : a ∈ commonDomain v) (b : M a),
          ¬ φ.Realize (valuesAt x hx) (Fin.snoc (valuesAt v hv) b)} ∈ (u : Filter α) := by
        filter_upwards [Ultrafilter.eventually_not.mpr hne] with a ha
        simp only [not_forall] at ha
        exact ha
      -- the counterexample, defined only on `T`: no nonemptiness of `M a` is needed
      let m : Section (u : Filter α) M :=
        ⟨_, hT, fun a ↦ a.2.choose_spec.choose_spec.choose⟩
      obtain ⟨a, ha, hTa⟩ := ((h m).and hT).exists
      have hv' : a ∈ commonDomain (Fin.snoc v m : Fin (k + 1) → Section (u : Filter α) M) :=
        (mem_commonDomain_snoc v m).2 ⟨hTa.choose_spec.choose, hTa⟩
      have := ha hTa.choose hv'
      rw [valuesAt_snoc v m hv' hTa.choose_spec.choose hTa] at this
      exact hTa.choose_spec.choose_spec.choose_spec this
    · intro h m
      filter_upwards [h] with a ha hx hv'
      obtain ⟨hv, hm⟩ := (mem_commonDomain_snoc v m).1 hv'
      rw [valuesAt_snoc v m hv' hv hm]
      exact ha hx hv _











/-- Here we need to enforce the finiteness of \beta somehow, this need to be fixed! -/
theorem realize_formula_cast {β : Type*} [Finite β] (φ : L.Formula β)
    (x : β → Section (u : Filter α) M) :
    (φ.Realize fun i ↦ (⟦x i⟧ : PartialProduct (u : Filter α) M)) ↔
      ∀ᶠ a : α in u, ∀ hx : a ∈ commonDomain x, φ.Realize (valuesAt x hx) := by
  let e : Fin 0 → Section (u : Filter α) M := Fin.elim0
  unfold Formula.Realize
  have hd : (default : Fin 0 → PartialProduct (u : Filter α) M) = fun i ↦ ⟦e i⟧ :=
    Subsingleton.elim _ _
  refine (iff_of_eq (congrArg (BoundedFormula.Realize φ fun i ↦
    (⟦x i⟧ : PartialProduct (u : Filter α) M)) hd)).trans
    ((boundedFormula_realize_cast φ x e).trans ?_)
  have he : ∀ a, a ∈ commonDomain e := fun a ↦ mem_iInter.2 fun i ↦ i.elim0
  refine eventually_congr (Eventually.of_forall fun a ↦ ⟨fun H hx ↦ ?_, fun H hx _ ↦ ?_⟩)
  · rw [Subsingleton.elim (default : Fin 0 → M a) (valuesAt e (he a))]
    exact H hx (he a)
  · rw [Subsingleton.elim (valuesAt e _) (default : Fin 0 → M a)]
    exact H hx

/-- Łoś's Theorem for a formula with names from any set `β`, possibly infinite. A formula
mentions only finitely many of its names, `φ.freeVarFinset`, so only the sections for those
names are intersected. On the right, `φ.restrictFreeVar id` is `φ` with its names taken from
that finite set: in `M a` it needs values only for the names it uses. -/
theorem realize_formula_cast' {β : Type*} [DecidableEq β] (φ : L.Formula β)
    (x : β → Section (u : Filter α) M) :
    (φ.Realize fun i ↦ (⟦x i⟧ : PartialProduct (u : Filter α) M)) ↔
      ∀ᶠ a : α in u, ∀ hx : a ∈ commonDomain (fun i : φ.freeVarFinset ↦ x i),
        Formula.Realize (φ.restrictFreeVar id : L.Formula φ.freeVarFinset)
          (valuesAt (fun i : φ.freeVarFinset ↦ x i) hx) :=
  -- in the partial ultraproduct, `φ` and its restriction are true together (Mathlib),
  -- and the restriction has finitely many names, so the finite version applies
  (BoundedFormula.realize_restrictFreeVar (f := id)
    (v := fun i : φ.freeVarFinset ↦ (⟦x i⟧ : PartialProduct (u : Filter α) M))
    (fun i ↦ (⟦x i⟧ : PartialProduct (u : Filter α) M)) fun _ ↦ rfl).symm.trans
    (realize_formula_cast _ fun i : φ.freeVarFinset ↦ x i)

/-- **Łoś's Theorem** for the partial product: a sentence is true in the partial ultraproduct
if and only if the set of structures it is true in is in the ultrafilter. Unlike Mathlib's
version, no structure `M a` needs to be nonempty. -/
theorem sentence_realize (φ : L.Sentence) :
    PartialProduct (u : Filter α) M ⊨ φ ↔ ∀ᶠ a : α in u, M a ⊨ φ := by
  let e : Empty → Section (u : Filter α) M := Empty.elim
  unfold Sentence.Realize
  have hd : (default : Empty → PartialProduct (u : Filter α) M) = fun i ↦ ⟦e i⟧ :=
    Subsingleton.elim _ _
  refine (iff_of_eq (congrArg (Formula.Realize φ) hd)).trans
    ((realize_formula_cast φ e).trans ?_)
  have he : ∀ a, a ∈ commonDomain e := fun a ↦ mem_iInter.2 fun i ↦ i.elim
  refine eventually_congr (Eventually.of_forall fun a ↦ ⟨fun H ↦ ?_, fun H _ ↦ ?_⟩)
  · rw [Subsingleton.elim (default : Empty → M a) (valuesAt e (he a))]
    exact H (he a)
  · rw [Subsingleton.elim (valuesAt e _) (default : Empty → M a)]
    exact H

/-! ### Comparison with Mathlib's ultraproduct

When every `M a` is nonempty, the partial ultraproduct is isomorphic to Mathlib's
`Filter.Product`. -/

/-- A function defined at every index, seen as a section whose domain is all of `α`. -/
def totalSection (f : ∀ a, M a) : Section (u : Filter α) M :=
  ⟨univ, univ_mem, fun a ↦ f a⟩

/-- From Mathlib's ultraproduct to the partial one. It is well defined: functions that agree
almost everywhere give sections that agree almost everywhere. -/
def ofProduct : (u : Filter α).Product M → PartialProduct (u : Filter α) M :=
  Quotient.lift (fun f ↦ (Quotient.mk _ (totalSection f) : PartialProduct (u : Filter α) M))
    fun _ _ h ↦ Quotient.sound (h.mono fun _ ha _ _ ↦ ha)

theorem ofProduct_mk (f : ∀ a, M a) :
    ofProduct (u := u) (Quotient.mk _ f) = Quotient.mk _ (totalSection f) :=
  rfl

/-- Finitely many elements of Mathlib's ultraproduct come from finitely many functions. -/
theorem exists_reps {n : ℕ} (x : Fin n → (u : Filter α).Product M) :
    ∃ g : Fin n → ∀ a, M a, x = fun i ↦ Quotient.mk _ (g i) :=
  ⟨fun i ↦ Quotient.out (x i), funext fun _ ↦ (Quotient.out_eq _).symm⟩

section Nonempty

variable [∀ a, Nonempty (M a)]

open Classical in
/-- A section extended to every index: its own value on its domain, a chosen element of
`M a` elsewhere. This is the only place where the structures must be nonempty. -/
noncomputable def extend (s : Section (u : Filter α) M) (a : α) : M a :=
  if h : a ∈ s.domain then s.value ⟨a, h⟩ else Classical.arbitrary (M a)

theorem extend_of_mem (s : Section (u : Filter α) M) {a : α} (h : a ∈ s.domain) :
    extend s a = s.value ⟨a, h⟩ :=
  dite_eq_left h

/-- From the partial ultraproduct to Mathlib's. It is well defined: two equivalent sections
agree almost everywhere on the overlap of their domains, which is in `u`, and the chosen
values outside the domains do not matter. -/
noncomputable def toProduct : PartialProduct (u : Filter α) M → (u : Filter α).Product M :=
  Quotient.lift (fun s ↦ (Quotient.mk _ (extend s) : (u : Filter α).Product M))
    fun s t h ↦ Quotient.sound <| by
      filter_upwards [h, s.large, t.large] with a ha hs ht
      rw [extend_of_mem s hs, extend_of_mem t ht]
      exact ha hs ht

theorem toProduct_mk (s : Section (u : Filter α) M) :
    toProduct (Quotient.mk _ s) = (Quotient.mk _ (extend s) : (u : Filter α).Product M) :=
  rfl

/-- Total function → section → total function gives back the same function. -/
theorem toProduct_ofProduct (x : (u : Filter α).Product M) : toProduct (ofProduct x) = x := by
  induction x using Quotient.inductionOn with
  | h f =>
    exact Quotient.sound (Eventually.of_forall fun a ↦ extend_of_mem (totalSection f) (mem_univ a))

/-- Section → total function → section gives a section equivalent to the first one: they agree
on its whole domain. -/
theorem ofProduct_toProduct (y : PartialProduct (u : Filter α) M) :
    ofProduct (toProduct y) = y := by
  induction y using Quotient.inductionOn with
  | h s =>
    exact Quotient.sound (Eventually.of_forall fun a _ h ↦ extend_of_mem s h)

/-- The two ultraproducts correspond one to one. -/
noncomputable def productEquiv : (u : Filter α).Product M ≃ PartialProduct (u : Filter α) M where
  toFun := ofProduct
  invFun := toProduct
  left_inv := toProduct_ofProduct
  right_inv := ofProduct_toProduct

/-- **Comparison with Mathlib.** When every `M a` is nonempty, Mathlib's ultraproduct and the
partial ultraproduct are isomorphic first-order structures. -/
noncomputable def productLEquiv :
    (u : Filter α).Product M ≃[L] PartialProduct (u : Filter α) M where
  toEquiv := productEquiv
  map_fun' := by
    intro n f x
    obtain ⟨g, rfl⟩ := exists_reps x
    -- both sides are computed index by index, with the same values
    exact (congrArg ofProduct (Ultraproduct.funMap_cast (u := u) f g)).trans
      ((Quotient.sound (Eventually.of_forall fun _ _ _ ↦ rfl)).trans
        (funMap_cast f fun i ↦ totalSection (g i)).symm)
  map_rel' := by
    intro n r x
    obtain ⟨g, rfl⟩ := exists_reps x
    refine (relMap_quotient_mk' (partialProductSetoid (u : Filter α) M) r
      fun i ↦ totalSection (g i)).trans
      (Iff.trans ?_ (relMap_quotient_mk' ((u : Filter α).productSetoid M) r g).symm)
    -- the sections are defined everywhere, so "where defined" adds nothing
    exact ⟨fun H ↦ H.mono fun a ha ↦ ha (mem_iInter.2 fun _ ↦ mem_univ a),
      fun H ↦ H.mono fun _ ha _ ↦ ha⟩

/-- Mathlib's Łoś's Theorem, recovered from the partial version through the isomorphism
`productLEquiv`, without using Mathlib's own proof. -/
theorem product_sentence_realize (φ : L.Sentence) :
    (u : Filter α).Product M ⊨ φ ↔ ∀ᶠ a : α in u, M a ⊨ φ :=
  (StrongHomClass.realize_sentence productLEquiv φ).trans (sentence_realize φ)

end Nonempty

end PartialUltraproduct

end Language

end FirstOrder
