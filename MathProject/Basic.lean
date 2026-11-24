import Mathlib

set_option linter.style.header false

/-!
# Filter products over "almost every" index

`Filter.Product F E` is the quotient of the *total* dependent functions `(i : α) → E i`
by the relation "equal on a set of indices in `F`". If even one fibre `E i` is empty,
there are no total functions at all, so the product is empty, even when the empty
fibres form a set that `F` ignores.

This file shows the problem on an example and then builds a version whose
representatives only need to be defined on some set in `F`.

## The problem

Mathlib's relation (`Filter.productSetoid`, a dependent version of `Filter.germSetoid`):

```
def productSetoid (l : Filter α) (ε : α → Type*) : Setoid ((a : _) → ε a) where
  r f g := ∀ᶠ a in l, f a = g a
```

The relation itself only looks at "almost every" index, but its representatives must be
defined at *every* index.

## The fix

Take as representatives the pairs `(D, f)` with `D ∈ F` and `f ∈ ∏_{i ∈ D} E i`, and set

  `(D, f) ∼_F (D', g)  ↔  {i ∈ D ∩ D' | f i = g i} ∈ F`.

Why this case is often ignored:
https://mathoverflow.net/questions/55989/ultraproducts-and-the-empty-set

## A related proposal from Zulip

```
instance : CoeSort (Filter α) (Type _) where coe f := f.sets
instance (f : Filter α) : CoeSort f (Type _) where coe s := s

def Filter.betterProductSetoid (l : Filter α) (ε : α → Type*) :
    Setoid ((s : l) × ((a : s) → ε a)) where
  r := fun ⟨s, f⟩ ⟨t, g⟩ => ∃ (u : l) (hs : u ≤ s) (ht : u ≤ t),
    ∀ x : u, f ⟨x, hs x.prop⟩ = g ⟨x, ht x.prop⟩
  iseqv := sorry

def Filter.betterProduct (l : Filter α) (ε : α → Type*) :=
  Quotient <| l.betterProductSetoid ε
```
-/

open Set Filter

namespace Product

/-! ## Example: one empty fibre empties Mathlib's product -/

/-- The fibre over `i` is `{0, 1, …, i - 1}`, so the fibre over `0` is empty. -/
def A (i : ℕ) := Finset.range i

/-- The fibre over `0` is empty. -/
theorem zero_fiber_is_empty : IsEmpty (A 0) :=
  ⟨fun n => List.not_mem_nil n.property⟩

/-- Whatever the filter (even one that ignores the index `0`), Mathlib's product of
the fibres `A i` is empty: a representative would need a value in `A 0`. -/
theorem mathlib_product_empty (F : Filter ℕ) :
    IsEmpty (Filter.Product F (fun i => (A i : Type))) := by
  constructor
  intro x
  unfold Filter.Product at x
  exact Quotient.inductionOn x (fun f => zero_fiber_is_empty.false (f 0))

/-! ## The product over a "almost everywhere" index-/

variable {α : Type*} (F : Filter α) (E : α → Type*)

/-- A section defined only on a set of indices that belongs to `F`. -/
structure Section where
  /-- The indices where the section is defined. -/
  domain : Set α
  /-- The domain is large: it belongs to the filter. -/
  large : domain ∈ F
  /-- The value at each index of the domain. -/
  value : (i : domain) → E i.val

/-- Two sections are equivalent when, for `F`-almost every index, they agree wherever
both are defined. -/
def partialProductSetoid : Setoid (Section F E) where
  r f g := ∀ᶠ i in F, ∀ (hf : i ∈ f.domain) (hg : i ∈ g.domain),
    f.value ⟨i, hf⟩ = g.value ⟨i, hg⟩
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · -- reflexive
      intro f
      exact Filter.Eventually.of_forall (fun _ _ _ => rfl)
    · -- symmetric
      intro f g h
      exact h.mono (fun _ hi hf hg => (hi hg hf).symm)
    · -- transitive: on the domain of `g`, which is large, chain the two equalities
      intro f g u hfg hgu
      filter_upwards [hfg, hgu, g.large] with i hi hj ht
      intro hf hu
      exact (hi hf ht).trans (hj ht hu)

/-- The partial filter product: sections on large sets, up to `partialProductSetoid`. -/
def PartialProduct := Quotient (partialProductSetoid F E)

end Product

noncomputable section

/--
Converts a Type into a nonstandard Type using an ultrafilter `U`,
for example `Ultra U ℕ` are non-standard natural numbers. -/
def Ultra {I : Type} (U : Ultrafilter I) (α : Type) : Type :=
  Product.PartialProduct (U : Filter I) (fun _ ↦ α)

namespace Ultra

variable {I : Type} {U : Ultrafilter I}

/-- The class of a section: the basic way to build an element of `Ultra U α`. -/
def mk {α : Type} (s : Product.Section (U : Filter I) (fun _ ↦ α)) : Ultra U α :=
  Quotient.mk _ s

/-- The section defined at every index by `f`. -/
def ofFun {α : Type} (f : I → α) : Ultra U α :=
  mk ⟨univ, univ_mem, fun i ↦ f i⟩

/-- Lifts an object into the nonstandard type -/
@[coe] def lift {α : Type} (a : α) : Ultra U α := ofFun (fun _ ↦ a)
instance {I : Type} (U : Ultrafilter I) (α : Type) : Coe α (Ultra U α) := ⟨Ultra.lift⟩

/-- `lift` of a standard number to nonstandard is injective: if `lift a₁ = lift a₂`,
then `a₁ = a₂` on a set in the ultrafilter, which is never empty. -/
theorem lift.inj {α : Type} : (Ultra.lift (U := U) (α := α)).Injective := by
  intro a₁ a₂ eq
  have h : ∀ᶠ i in (U : Filter I), ∀ (_ : i ∈ univ) (_ : i ∈ univ), a₁ = a₂ :=
    Quotient.exact eq
  obtain ⟨i, hi⟩ := h.exists
  exact hi trivial trivial

/-- If `α` is finite, every nonstandard object can be represented with a standard one:
the domain is a finite union of the sets where the section takes each value, and an
ultrafilter contains one piece of any finite union it contains. -/
theorem lift.surj {α : Type} [Finite α] : (lift (U := U) (α := α)).Surjective := by
  intro x
  induction x using Quotient.inductionOn with | h s => ?_
  -- S a: the indices where the section is defined and takes the value `a`
  let S : α → Set I := fun a ↦ {i | ∃ h : i ∈ s.domain, s.value ⟨i, h⟩ = a}
  -- the finitely many sets `S a` cover the domain, so the ultrafilter contains one of them
  have hcover : (⋃ a ∈ (univ : Set α), S a) ∈ U := by
    apply Filter.mem_of_superset s.large
    intro i hi
    simp only [mem_iUnion]
    exact ⟨s.value ⟨i, hi⟩, trivial, hi, rfl⟩
  obtain ⟨a, -, ha⟩ := (Ultrafilter.finite_biUnion_mem_iff finite_univ).mp hcover
  refine ⟨a, Quotient.sound ?_⟩
  show ∀ᶠ i in (U : Filter I), ∀ (_ : i ∈ univ) (h : i ∈ s.domain),
    a = s.value ⟨i, h⟩
  filter_upwards [ha] with i ⟨h, hv⟩
  intro _ _
  exact hv.symm

/-- On finite types, `lift` between `α` and `Ultra U α` as an isomorphism. -/
def liftFin {α : Type} [Finite α] : α ≃ Ultra U α :=
  .ofBijective Ultra.lift ⟨Ultra.lift.inj, Ultra.lift.surj⟩
/-- Conversion of a finite `Ultra U α` back to `α` -/
def std {α : Type} [Finite α] (a : Ultra U α) : α := liftFin.symm a

/-- Function application of nonstandard objects: the result is defined where both
sections are, a set in the filter because filters are closed under intersections. -/
def app {α : Type} {β : Type} (f : Ultra U (α → β)) (a : Ultra U α) : Ultra U β :=
  Quotient.lift₂
    (fun f' a' ↦ mk ⟨f'.domain ∩ a'.domain, inter_mem f'.large a'.large,
      fun i ↦ f'.value ⟨i, i.2.1⟩ (a'.value ⟨i, i.2.2⟩)⟩)
    (by
      intro f₁ a₁ f₂ a₂ hf ha
      apply Quotient.sound
      show ∀ᶠ i in (U : Filter I), _
      filter_upwards [hf, ha] with i h₁ h₂
      intro p q
      simp only [h₁ p.1 q.1, h₂ p.2 q.2])
    f a

/--
Nonstandard functions do not contain any extra data that cannot be seen by applying.
This is needed for a `FunLike` instance.
-/
theorem app.inj {α β : Type} (f₁ f₂ : Ultra U (α → β)) (eq : app f₁ = app f₂) : f₁ = f₂ := by
  induction f₁ using Quotient.inductionOn with | h s₁ => ?_
  induction f₂ using Quotient.inductionOn with | h s₂ => ?_
  apply Quotient.sound
  show ∀ᶠ i in (U : Filter I), ∀ (h₁ : i ∈ s₁.domain) (h₂ : i ∈ s₂.domain),
    s₁.value ⟨i, h₁⟩ = s₂.value ⟨i, h₂⟩
  by_contra hne
  -- T: the indices where both are defined and some point `x` tells them apart
  have hT : {i | ∃ (h₁ : i ∈ s₁.domain) (h₂ : i ∈ s₂.domain) (x : α),
      s₁.value ⟨i, h₁⟩ x ≠ s₂.value ⟨i, h₂⟩ x} ∈ (U : Filter I) := by
    have hc := Ultrafilter.compl_mem_iff_notMem.mpr hne
    filter_upwards [hc] with i hi
    simp only [mem_compl_iff, mem_ofPred_eq, not_forall] at hi
    obtain ⟨h₁, h₂, hne'⟩ := hi
    exact ⟨h₁, h₂, Function.ne_iff.mp hne'⟩
  -- the witness: defined only on T, picks such a point at each index
  let a : Ultra U α := mk ⟨_, hT, fun i ↦ i.2.choose_spec.choose_spec.choose⟩
  have h : ∀ᶠ i in (U : Filter I), _ := Quotient.exact (congrFun eq a)
  obtain ⟨i, hi, hTi⟩ := (h.and hT).exists
  exact hTi.choose_spec.choose_spec.choose_spec
    (hi ⟨hTi.choose, hTi⟩ ⟨hTi.choose_spec.choose, hTi⟩)

-- Automatically treat packed functions of type `Ultra U (α → β)`
-- as functions `Ultra U α → Ultra U β`
instance {I : Type} (U : Ultrafilter I) (α β : Type) :
    FunLike (Ultra U (α → β)) (Ultra U α) (Ultra U β) where
  coe := app
  coe_injective := app.inj

/-- The diagonal: the index set seen inside its own extension. -/
def diag (U : Ultrafilter I) : Ultra U I := ofFun id

/-- For a free ultrafilter the diagonal is non-standard: it equals `lift i` only on `{i}`,
and a free ultrafilter contains no finite set. -/
theorem diag_ne_lift (hU : (U : Filter I) ≤ .cofinite) (i : I) : diag U ≠ lift i := by
  intro eq
  have h : ∀ᶠ j in (U : Filter I), ∀ (_ : j ∈ univ) (_ : j ∈ univ), j = i :=
    Quotient.exact eq
  obtain ⟨j, hj, hne⟩ := (h.and (hU (Filter.eventually_cofinite_ne i))).exists
  exact hne (hj trivial trivial)

end Ultra

-- Allow writing `a < b` for `a b : Ultra U α`
instance {I : Type} (U : Ultrafilter I) (α : Type) [LT α] : LT (Ultra U α) where
  lt a b := (Ultra.lift LT.lt a b).std

/-! ## Test case: the index set `ℕ` -/

section NatTest

variable (U : Ultrafilter ℕ)

/-- Inside this section, `∗α` means `Ultra U α` for the fixed ultrafilter `U`. -/
local notation "∗" α:max => Ultra U α

/-- A nonstandard natural number: the diagonal for the index set `ℕ`. -/
def big : ∗ℕ := Ultra.diag U

/-- `big` is non-standard, as a case of the general `diag_ne_lift`. -/
example (hU : (U : Filter ℕ) ≤ .cofinite) (n : ℕ) : big U ≠ (n : ∗ℕ) :=
  Ultra.diag_ne_lift hU n

/-- Applying a nonstandard function to a nonstandard number. -/
example (f : ∗(ℕ → ℕ)) (x : ∗ℕ) : ∗ℕ := f x

/-- Nonstandard natural number `big` is bigger than all standard natural numbers. -/
theorem big_gt (hU : (U : Filter ℕ) ≤ .cofinite) (n : ℕ) : (n : ∗ℕ) < big U := by
  -- `U` refines the Fréchet filter, so it contains every cofinite set,
  -- in particular `{i | n < i}`, whose complement `{i | i ≤ n}` is finite
  have hev : ∀ᶠ i in (U : Filter ℕ), n < i :=
    hU (Filter.eventually_cofinite.mpr
      ((Set.finite_le_nat n).subset fun _ hi ↦ not_lt.mp hi))
  -- so the comparison `n < big` is true on a set in the ultrafilter
  have hx : Ultra.app (Ultra.app (Ultra.lift (U := U) (LT.lt : ℕ → ℕ → Prop))
      (Ultra.lift n)) (big U) = Ultra.lift True := by
    apply Quotient.sound
    show ∀ᶠ i in (U : Filter ℕ), _
    filter_upwards [hev] with i hi
    intro _ _
    simpa using hi
  have hstd : Ultra.std (Ultra.lift (U := U) True) = True :=
    Ultra.liftFin.symm_apply_apply True
  change Ultra.std (Ultra.app (Ultra.app (Ultra.lift (U := U) (LT.lt : ℕ → ℕ → Prop))
    (Ultra.lift n)) (big U))
  rw [hx, hstd]
  trivial

end NatTest

/-- Example: Mathlib's free ultrafilter `hyperfilter ℕ` (built from the Fréchet filter). -/
example (n : ℕ) : (n : Ultra (hyperfilter ℕ) ℕ) < big (hyperfilter ℕ) :=
  big_gt (hyperfilter ℕ) hyperfilter_le_cofinite n

end
