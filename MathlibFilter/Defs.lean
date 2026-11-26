/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jeremy Avigad
-/
module

public import Mathlib.Order.BooleanAlgebra.Set
public import Mathlib.Order.Bounds.Defs
public import Mathlib.Order.SetNotation

/-!
# Definitions about filters

A *filter* on a type `α` is a collection of sets of `α` which contains the whole `α`,
is upwards-closed, and is stable under intersection. Filters are mostly used to
abstract two related kinds of ideas:
* *limits*, including finite or infinite limits of sequences, finite or infinite limits of functions
  at a point or at infinity, etc...
* *things happening eventually*, including things happening for large enough `n : ℕ`, or near enough
  a point `x`, or for close enough pairs of points, or things happening almost everywhere in the
  sense of measure theory. Dually, filters can also express the idea of *things happening often*:
  for arbitrarily large `n`, or at a point in any neighborhood of given a point etc...

## Main definitions

* `Filter` : filters on a set;
* `Filter.principal`, `𝓟 s` : filter of all sets containing a given set;
* `Filter.map`, `Filter.comap` : operations on filters;
* `Filter.Tendsto` : limit with respect to filters;
* `Filter.Eventually` : `f.Eventually p` means `{x | p x} ∈ f`;
* `Filter.Frequently` : `f.Frequently p` means `{x | ¬p x} ∉ f`;
* `filter_upwards [h₁, ..., hₙ]` :
  a tactic that takes a list of proofs `hᵢ : sᵢ ∈ f`,
  and replaces a goal `s ∈ f` with `∀ x, x ∈ s₁ → ... → x ∈ sₙ → x ∈ s`;
* `Filter.NeBot f` : a utility class stating that `f` is a non-trivial filter.
* `Filter.IsBounded r f`: the filter `f` is eventually bounded w.r.t. the relation `r`,
  i.e. eventually, it is bounded by some uniform bound.
  `r` will be usually instantiated with `(· ≤ ·)` or `(· ≥ ·)`.
* `Filter.IsCobounded r f` states that the filter `f` does not tend to infinity w.r.t. `r`.
  This is also called frequently bounded. Will be usually instantiated with `(· ≤ ·)` or `(· ≥ ·)`.

## Notation

* `∀ᶠ x in f, p x` : `f.Eventually p`;
* `∃ᶠ x in f, p x` : `f.Frequently p`;
* `f =ᶠ[l] g` : `∀ᶠ x in l, f x = g x`;
* `f ≤ᶠ[l] g` : `∀ᶠ x in l, f x ≤ g x`;
* `𝓟 s` : `Filter.Principal s`, localized in `Filter`.

## Implementation Notes

Important note: Bourbaki requires that a filter on `X` cannot contain all sets of `X`,
which we do *not* require.
This gives `Filter X` better formal properties,
in particular a bottom element `⊥` for its lattice structure,
at the cost of including the assumption `[NeBot f]` in a number of lemmas and definitions.

## References

*  [N. Bourbaki, *General Topology*][bourbaki1966]
-/

@[expose] public section

assert_not_exists RelIso

open Set

/-- A filter `F` on a type `α` is a collection of sets of `α` which contains the whole `α`,
is upwards-closed, and is stable under intersection. We do not forbid this collection to be
all sets of `α`.i.e the powerset of α. Such filter is called improper in literature. -/
@[to_dual_dont_translate]
structure Filter (α : Type*) where
  /-- The set of sets that belong to the filter. -/
  sets : Set (Set α)
  /-- The set `Set.univ` belongs to any filter. -/
  univ_sets : Set.univ ∈ sets
  /-- If a set belongs to a filter, then its superset belongs to the filter as well. -/
  sets_of_superset {x y} : x ∈ sets → x ⊆ y → y ∈ sets
  /-- If two sets belong to a filter, then their intersection belongs to the filter as well. -/
  inter_sets {x y} : x ∈ sets → y ∈ sets → x ∩ y ∈ sets

namespace Filter

variable {α β : Type*} {f g : Filter α} {s t : Set α}

/-- Some equivalences: if the filters have the same members, they are the same -/
theorem filter_eq : ∀ {f g : Filter α}, f.sets = g.sets → f = g
  | ⟨_, _, _, _⟩, ⟨_, _, _, _⟩, rfl => rfl

/-- If `F` is a filter on `α`, and `U` a subset of `α` then we can write `U ∈ F` as on paper. -/
instance instMembership : Membership (Set α) (Filter α) := ⟨fun F U => U ∈ F.sets⟩


@[ext]
protected theorem ext (h : ∀ s, s ∈ f ↔ s ∈ g) : f = g := filter_eq <| Set.ext h

/-- Let `t : Set (Set α)` be a family of sets, and let `h₁`, `h₂`, `h₃`
be proofs that `t` satisfies the three filter axioms.

The constructor `Filter.mk` (where `mk` stands for "make") constructs
a filter from the family `t` together with these proofs. Lean automatically
generates `mk` as the default constructor of a structure.

This theorem states that a set belongs to the constructed filter if and
only if it belongs to the underlying family `t`.

On paper, we would simply identify the filter `F` with the family `t`.
In Lean, however, a filter is a structure containing both the family
of sets and the proofs of the filter axioms.

The attribute `@[simp]` allows Lean to automatically simplify membership
in the constructed filter to membership in `t`.

The proof is `Iff.rfl` since the two propositions are definitionally equal. -/
@[simp]
protected theorem mem_mk {t : Set (Set α)} {h₁ h₂ h₃} : s ∈ mk t h₁ h₂ h₃ ↔ s ∈ t :=
  Iff.rfl

/-- Recall that a filter `f : Filter α` is a structure whose field
`f.sets : Set (Set α)` is the underlying family of sets.

The membership notation `s ∈ f` is defined through the instance
`Filter.instMembership`, which identifies membership in a filter
with membership in its underlying family of sets.

This theorem states that a set `s` belongs to the underlying family
`f.sets` if and only if it belongs to the filter `f` itself.

On paper, we do not distinguish between a filter and its underlying
family of sets. In Lean, however, the former is a structure, whereas
the latter is one of its fields.

The attribute `@[simp]` allows Lean to automatically simplify
`s ∈ f.sets` to the more natural mathematical notation `s ∈ f`.

The proof is `Iff.rfl` since the two propositions are definitionally
equal by the membership instance. -/
@[simp]
protected theorem mem_sets : s ∈ f.sets ↔ s ∈ f :=
  Iff.rfl

/-- The following expose the interesting properties of the filters.
These are simply a better way to acces the axioms.
First axiom: -/
@[simp]
theorem univ_mem : univ ∈ f :=
  f.univ_sets

/-- Second axiom:
The attribute `@[gcongr]` allows the generalized congruence
tactic to exploit the monotonicity of filter membership
with respect to set inclusion. -/
@[gcongr]
theorem mem_of_superset {x y : Set α} (hx : x ∈ f) (hxy : x ⊆ y) : y ∈ f :=
  f.sets_of_superset hx hxy

/-- Consequence of the first two axioms -/
theorem univ_mem' (h : ∀ a, a ∈ s) : s ∈ f :=
  mem_of_superset univ_mem fun x _ => h x

/-- Third axiom: -/
theorem inter_mem (hs : s ∈ f) (ht : t ∈ f) : s ∩ t ∈ f :=
  f.inter_sets hs ht

/-- Modus ponens for filters -/
theorem mp_mem (hs : s ∈ f) (h : { x | x ∈ s → x ∈ t } ∈ f) : t ∈ f :=
  mem_of_superset (inter_mem hs h) fun _ ⟨h₁, h₂⟩ => h₂ h₁

/-- Override `sets` field of a filter to provide better definitional equality. -/
protected def copy (f : Filter α) (S : Set (Set α)) (hmem : ∀ s, s ∈ S ↔ s ∈ f) : Filter α where
  sets := S
  -- Transfer the first filter axiom from f to S.
  univ_sets := (hmem univ).2 univ_mem
   -- Transfer upward closure from f to S.
  sets_of_superset {x y} h hsub := (hmem y).2 <| mem_of_superset ((hmem x).1 h) hsub
  -- Transfer intersection closure from f to S.
  inter_sets {x y} h₁ h₂ := (hmem (x ∩ y)).2 <| inter_mem ((hmem x).1 h₁) ((hmem y).1 h₂)

@[simp] theorem mem_copy {S hmem} : s ∈ f.copy S hmem ↔ s ∈ S := Iff.rfl

/-- Construct a filter from a property that is stable under finite unions.
A set `s` belongs to `Filter.comk p _ _ _` iff its complement satisfies the predicate `p`.
This constructor is useful to define filters like `Filter.cofinite`.

The name `comk` can be understood as "complement make".

Unlike `Filter.mk`, which constructs a filter directly from
a family satisfying the filter axioms, `Filter.comk` constructs
a filter from a predicate `p` satisfying the dual axioms.

More precisely, we require that:
- the empty set satisfies `p`;
- `p` is downward closed under inclusion;
- `p` is stable under finite unions.

These are precisely the axioms of an ideal of sets
(without requiring properness).

We then construct a filter by taking all sets whose
complements satisfy `p`.

The filter axioms follow from the properties of complements
and De Morgan's laws. -/
def comk
    (p : Set α → Prop)
    (he : p ∅)
    (hmono : ∀ t, p t → ∀ s ⊆ t, p s)
    (hunion : ∀ s, p s → ∀ t, p t → p (s ∪ t)) : Filter α where
  sets := {t | p tᶜ}
  univ_sets := by simpa
  sets_of_superset := fun ht₁ ht => hmono _ ht₁ _ (compl_subset_compl.2 ht)
  inter_sets := fun ht₁ ht₂ => by simp [hunion _ ht₁ _ ht₂]

@[simp]
lemma mem_comk {p : Set α → Prop} {he hmono hunion s} :
    s ∈ comk p he hmono hunion ↔ p sᶜ :=
  .rfl

/-- The principal filter of `s` is the collection of all supersets of `s`. -/
def principal (s : Set α) : Filter α where
  sets := { t | s ⊆ t }
  univ_sets := subset_univ s
  sets_of_superset hx := Subset.trans hx
  inter_sets := subset_inter

@[inherit_doc]
scoped notation "𝓟" => Filter.principal
/-- From now on it will be 𝓟 t
Note that in the literature sometimes principal filters are generated by one element.
Here we allow it to be a set. Pure is the correct definition for that. -/
@[simp] theorem mem_principal : s ∈ 𝓟 t ↔ t ⊆ s := Iff.rfl

/-- `pure x` is the set of sets that contain `x`. It is equal to `𝓟 {x}` but
with this definition we have `s ∈ pure a` defeq `a ∈ s`. -/
instance : Pure Filter where
  pure x := .copy (𝓟 {x}) {s | x ∈ s} fun _ ↦ by simp

@[simp]
theorem mem_pure {a : α} {s : Set α} : s ∈ (pure a : Filter α) ↔ a ∈ s :=
  Iff.rfl

/-- The *kernel* of a filter is the intersection of all its sets. -/
def ker (f : Filter α) : Set α := ⋂₀ f.sets

/-- Double check -/
theorem principal_has_set_kernel (t : Set α) : ker (𝓟 t) = t := by
  unfold ker
  ext x
  constructor
  · intro hx
    exact Set.mem_sInter.mp hx t (mem_principal.mpr (Subset.rfl))
  · intro hx
    apply Set.mem_sInter.mpr
    intro s hs
    exact (mem_principal.mp hs) hx

/-- Given a filter `f` on the space of filters over `α`,
we construct a filter on `α` called the join of `f`.

A set `s : Set α` belongs to `join f` if and only if
the family of all filters containing `s` belongs to `f`.

In other words, `s` belongs to `join f` if it belongs
to `f`-almost every filter on `α`.

The construction can be understood as flattening a filter
of filters into a single filter.

The filter axioms follow by applying the corresponding
axioms at two different levels:
- to individual filters on `α`;
- to the outer filter on `Filter α`.

When restricted to ultrafilters, this construction is
closely related to the notion of an ultrafilter limit. -/
def join (f : Filter (Filter α)) : Filter α where
  sets := { s | { t : Filter α | s ∈ t } ∈ f }
  -- Every filter contains the whole space.
  univ_sets := by
    simp only [mem_ofPred_eq, univ_mem, ofPred_true]
  -- Every filter containing x also contains its superset y.
  sets_of_superset hx xy :=
    mem_of_superset hx fun f h => mem_of_superset h xy
  -- Every filter containing both x and y contains
  -- their intersection.
  inter_sets hx hy :=
    mem_of_superset (inter_mem hx hy)
      fun f ⟨h₁, h₂⟩ => inter_mem h₁ h₂

@[simp]
theorem mem_join {s : Set α} {f : Filter (Filter α)} : s ∈ join f ↔ { t | s ∈ t } ∈ f :=
  Iff.rfl

/-- Here we can furthermore note that pure takes a set as singleton as well. -/
example (g : Filter α) : join (pure g) = g := by
  ext s
  rw [mem_join, mem_pure]
  rfl


/-- The set of filters on `α` is equipped with a partial order
given by reverse inclusion of their underlying families of sets.

We say that a filter `f` is finer than a filter `g`, and write
`f ≤ g`, if every member of `g` also belongs to `f`.

Notice that a filter containing more sets is smaller with
respect to this partial order.

The partial order axioms follow directly from the corresponding
properties of set inclusion. Since we are working with reverse
inclusion, the order of the hypotheses is reversed when applying
`Subset.antisymm` and `Subset.trans`.

In the proof of antisymmetry, `filter_eq` allows us to deduce
equality of filters from equality of their underlying families
of sets. -/
instance : PartialOrder (Filter α) where
  le f g := ∀ ⦃U : Set α⦄, U ∈ g → U ∈ f
  le_antisymm a b h₁ h₂ := filter_eq <| Subset.antisymm h₂ h₁
  le_refl a := Subset.rfl
  le_trans a b c h₁ h₂ := Subset.trans h₂ h₁

/-- Unfolding the definition of the partial order on filters,
`f ≤ g` means that every set belonging to `g` also belongs
to `f`.

On paper, this would simply be written as
`f ≤ g ↔ g ⊆ f`, identifying filters with their underlying
families of sets.

The proof is `Iff.rfl` since the two propositions are
definitionally equal. -/
theorem le_def : f ≤ g ↔ ∀ x ∈ g, x ∈ f :=
  Iff.rfl

/-- The supremum of an arbitrary family `S` of filters is
the intersection of the filters belonging to `S`.

Recall that filters are ordered by reverse inclusion.
Therefore, the intersection of a family of filters is
its supremum rather than its infimum.

Instead of constructing this intersection directly,
Mathlib uses two previously defined operations:

- `𝓟 S` constructs the principal filter generated by `S`
  on the space `Filter α`;
- `join` transforms this filter of filters into a filter on `α`.

Unfolding these two definitions, a set `s` belongs to
`join (𝓟 S)` if and only if every filter belonging to `S`
contains `s`.

On paper, we would simply write the supremum of `S`
as the intersection of all its members. -/
instance instSupSet : SupSet (Filter α) where
  sSup S := join (𝓟 S)

@[simp] theorem mem_sSup {S : Set (Filter α)} : s ∈ sSup S ↔ ∀ f ∈ S, s ∈ f := .rfl

/-- The infimum of an arbitrary family `s` of filters is
defined as the supremum of all its lower bounds.

Recall that filters are ordered by reverse inclusion.
Consequently, a lower bound of `s` is a filter containing
every filter belonging to `s`.

Since the supremum of a family of filters is its
intersection, the infimum is the intersection of all
filters containing every member of `s`.

On paper, we would describe this as the filter generated
by the union of all filters belonging to `s`.

Notice that we cannot simply take the union of these
filters, since their union need not be closed under
finite intersections.

The attribute `@[irreducible]` prevents Lean from
automatically unfolding this definition during ordinary
definitional equality checks and unification.

The keyword `protected` allows us to distinguish this
specific construction, `Filter.sInf`, from the generic
operation `sInf` provided by the `InfSet` typeclass. -/
@[irreducible]
protected def sInf (s : Set (Filter α)) : Filter α :=
  sSup (lowerBounds s)

instance instInfSet : InfSet (Filter α) where
  sInf := Filter.sInf

/-- The infimum of a family of filters is the supremum
of the family of its lower bounds.

On paper, this equality holds immediately by definition.

In Lean, however, `Filter.sInf` is marked as `@[irreducible]`,
so its definition is not automatically unfolded during
ordinary definitional equality checks.

This theorem provides an explicit way to access the
underlying definition of the infimum.

The proof unfolds both the generic operation `sInf`,
provided by the `InfSet` typeclass, and the specific
implementation `Filter.sInf`. After unfolding these
definitions, the two sides coincide. -/
protected theorem sSup_lowerBounds (s : Set (Filter α)) :
    sSup (lowerBounds s) = sInf s := by
  simp [sInf, Filter.sInf]

/-- The greatest element of the lattice of filters is the
filter consisting only of the whole space.

Recall that filters are ordered by reverse inclusion.
Since every filter contains the whole space, every filter
is smaller than `⊤` with respect to this partial order.

Mathlib constructs `⊤` as the supremum of all principal
point filters. Indeed, `Set.range pure` is the family
of filters generated by singletons.

Since the supremum of filters is their intersection,
a set belongs to this supremum if and only if it contains
every point of the underlying type.

On paper, we would simply write `⊤ = {X}`.

The `copy` operation is used to replace the underlying
family of sets with the equivalent but definitionally
more convenient representation `{s | ∀ x, x ∈ s}`.

The tactic `simp` proves that these two representations
have exactly the same members.

The notation `.copy` refers to `Filter.copy`, with the
namespace inferred by Lean from the expected type. -/
instance : Top (Filter α) where
  top := .copy (sSup (Set.range pure))
    {s | ∀ x, x ∈ s} <| by simp

theorem mem_top_iff_forall {s : Set α} : s ∈ (⊤ : Filter α) ↔ ∀ x, x ∈ s :=
  Iff.rfl

@[simp]
theorem mem_top {s : Set α} : s ∈ (⊤ : Filter α) ↔ s = univ := by
  rw [mem_top_iff_forall, eq_univ_iff_forall]

/-- The least element of the lattice of filters is the
filter containing every subset of `α`, including `∅`.

Mathlib constructs `⊥` as the supremum of the empty family
of filters. By `mem_sSup`, a set `s` belongs to `sSup ∅`
if and only if `∀ f ∈ ∅, s ∈ f`, which holds vacuously.
Hence every set belongs to `sSup ∅`.

Compare with `⊤ = sSup (Set.range pure)`:
- `s ∈ ⊤` iff every point belongs to `s`, so only `univ`;
- `s ∈ ⊥` always, so every set.

Recall that `f ≤ g` means every member of `g` belongs to `f`.
Since `⊥` contains every set, `⊥ ≤ f` for every filter `f`.

On paper, we would simply write `⊥ = 𝒫(X)`.

As for `⊤`, `copy` replaces the underlying family of sets
with `univ`, so that `s ∈ ⊥` unfolds to `s ∈ univ`, which is
`True` by definition. This is why `mem_bot` is proved by
`trivial`.

Since `∅ ∈ ⊥`, the statement `∀ᶠ x in ⊥, p x` holds for every
`p`, even `False`: `⊥` behaves like a contradiction.
Bourbaki excludes it from the definition of a filter; Mathlib
keeps it so that filters form a complete lattice, and uses
the class `NeBot` (see below) when `∅ ∉ f` is needed. -/
instance : Bot (Filter α) where
  bot := .copy (sSup ∅) univ <| by simp

@[simp]
theorem mem_bot {s : Set α} : s ∈ (⊥ : Filter α) :=
  trivial

/-- The infimum of filters is the filter generated by intersections
  of elements of the two filters.

A set `s` belongs to `f ⊓ g` if `s = a ∩ b` exactly, for some
`a ∈ f` and `b ∈ g`.

We cannot simply take the union of the two families, since it is
not closed under intersections. Example on `ℕ`:
`f = 𝓟 {0,1}`, `g = 𝓟 {1,2}`; then `{0,1}` and `{1,2}` belong to
the union, but `{1}` belongs to neither. Here `f ⊓ g = 𝓟 {1}`.

Every `a ∈ f` is `a ∩ univ`, so `f ⊓ g ≤ f`; similarly `f ⊓ g ≤ g`.
Any filter containing the members of `f` and `g` contains every
`a ∩ b`, so `f ⊓ g` is the greatest lower bound.

The three axioms:
- `univ = univ ∩ univ`, proved by `simp`.
- Superset: the definition asks for an equality `s = a ∩ b`, so
  given `x = a ∩ b ⊆ y` we must write `y` itself as an intersection:
  `y = (a ∪ y) ∩ (b ∪ y)`, since this is `(a ∩ b) ∪ y = x ∪ y = y`.
  Here `a ∪ y ∈ f` and `b ∪ y ∈ g` as supersets of `a` and `b`.
  We cannot take `y` directly: `y ∈ f` would need `a ⊆ y`.
  Example: `a = {0,1}`, `b = {1,2}`, `y = {1,5}`:
  `{0,1,5} ∩ {1,2,5} = {1,5}`.
- Intersection: `(a ∩ b) ∩ (c ∩ d) = (a ∩ c) ∩ (b ∩ d)`, with
  `a ∩ c ∈ f` and `b ∩ d ∈ g`; `ac_rfl` proves the equality by
  associativity and commutativity of `∩`.

On paper: `s ∈ f ⊓ g ↔ ∃ a ∈ f, ∃ b ∈ g, a ∩ b ⊆ s`, equivalent
to the definition by the superset argument above. -/
instance instInf : Min (Filter α) :=
  ⟨fun f g : Filter α =>
    { sets := { s | ∃ a ∈ f, ∃ b ∈ g, s = a ∩ b }
      univ_sets := ⟨_, univ_mem, _, univ_mem, by simp⟩
      sets_of_superset := by
        rintro x y ⟨a, ha, b, hb, rfl⟩ xy
        refine ⟨a ∪ y, mem_of_superset ha subset_union_left, b ∪ y,
          mem_of_superset hb subset_union_left, ?_⟩
        rw [← inter_union_distrib_right, union_eq_self_of_subset_left xy]
      inter_sets := by
        rintro x y ⟨a, ha, b, hb, rfl⟩ ⟨c, hc, d, hd, rfl⟩
        refine ⟨a ∩ c, inter_mem ha hc, b ∩ d, inter_mem hb hd, ?_⟩
        ac_rfl }⟩

/-- The supremum of two filters is the filter that contains sets that belong to both filters.

It reuses `sSup`: by `mem_sSup`,
`s ∈ sSup {f, g} ↔ ∀ h ∈ {f, g}, s ∈ h ↔ s ∈ f ∧ s ∈ g`,
and `simp` proves this equivalence. As for `⊤` and `⊥`, `copy`
makes `s ∈ f ⊔ g` unfold directly to `s ∈ f ∧ s ∈ g`.

Unlike `⊓`, no trick is needed: the common part of two filters is
already a filter (if `s`, `t` are in both, so is `s ∩ t`).
Keeping only what two filters share creates no new sets.

Example on `ℕ`: `f = 𝓟 {0,1}`, `g = 𝓟 {1,2}`. Then
`s ∈ f ⊔ g ↔ {0,1} ⊆ s ∧ {1,2} ⊆ s ↔ {0,1,2} ⊆ s`,
so `f ⊔ g = 𝓟 {0,1,2}`. Also `pure 0 ⊔ pure 1 = 𝓟 {0,1}`.

For principal filters the operations follow the generating sets:
- `𝓟 s ⊓ 𝓟 t = 𝓟 (s ∩ t)`;
- `𝓟 s ⊔ 𝓟 t = 𝓟 (s ∪ t)`;
- `𝓟 s ≤ 𝓟 t ↔ s ⊆ t`.
A finer filter is "concentrated on a smaller set".

Least upper bound: `f ≤ f ⊔ g` since every set of `f ⊔ g` is in
`f` (same for `g`); and if `f ≤ h`, `g ≤ h`, every set of `h` is in
`f` and in `g`, hence in `f ⊔ g`, so `f ⊔ g ≤ h`. -/
instance instSup : Max (Filter α) where
  max f g := .copy (sSup {f, g}) {s | s ∈ f ∧ s ∈ g} <| by simp

/-- The relative complement of two filters `f \ g` contains sets
whose union with any set in `g` lies in `f`.

Definition used: `s ∈ f \ g ↔ ∀ t ∈ g, s ⊆ t → t ∈ f`.
The two descriptions agree: if `t ∈ g` then `s ∪ t ∈ g` and
`s ⊆ s ∪ t`; conversely if `s ⊆ t` then `t = s ∪ t`.

What it is for: `f \ g` is the smallest filter `h` (in the filter
order) with `f ≤ g ⊔ h`; precisely, `f \ g ≤ h ↔ f ≤ g ⊔ h`.
Proof sketch:
- (⇐) if `s ∈ h`, `t ∈ g`, `s ⊆ t`, then `t ∈ h` (superset), so `t`
  is in `g ⊔ h`, hence in `f`.
- (⇒) if `t ∈ g ⊔ h`, then `t ∈ h ⊆ f \ g`; apply the definition
  with `t` itself (`t ∈ g`, `t ⊆ t`) to get `t ∈ f`.
This makes filters a *co-Heyting algebra*; it is rarely used.

Example on `ℕ`: `𝓟 {0,1} \ 𝓟 {1} = 𝓟 {0}`. In general
`𝓟 a \ 𝓟 b = 𝓟 (a \ b)`: taking `t = s ∪ b`, the condition says
exactly `a ⊆ s ∪ b`, i.e. `a \ b ⊆ s`.

The three axioms:
- `univ`: if `univ ⊆ t` then `t = univ ∈ f` (`simp +contextual`).
- Superset: if `x ⊆ y ⊆ t` with `t ∈ g`, use `x ⊆ t` and `hx`.
- Intersection: the same trick as for `⊓`. Given `x ∩ y ⊆ t ∈ g`,
  write `t = (x ∪ t) ∩ (y ∪ t)`; `x ∪ t ∈ g` and contains `x`,
  so it is in `f` by `hx`; same for `y ∪ t`; then use `inter_mem`. -/
instance instSDiff : SDiff (Filter α) where
  sdiff f g := {
    sets := {s | ∀ ⦃t⦄, t ∈ g → s ⊆ t → t ∈ f}
    univ_sets := by simp +contextual
    sets_of_superset hx hxy t ht hyt := hx ht (hxy.trans hyt)
    inter_sets hx hy t htg ht := by
      rw [← union_eq_right.2 ht, inter_union_distrib_right]
      apply inter_mem
      · exact hx (mem_of_superset htg subset_union_right) subset_union_left
      · exact hy (mem_of_superset htg subset_union_right) subset_union_left
  }

/-- The coheyting negation of a filter is the complement of its kernel.

`￢f = 𝓟 (ker f)ᶜ`: the sets containing every point outside the
kernel (the kernel `ker f` is the intersection of all sets of `f`).

In a co-Heyting algebra `￢f = ⊤ \ f`, and this holds here:
`s ∈ ⊤ \ f` means every `t ∈ f` with `s ⊆ t` is `univ`.
- If `x ∉ s` and `x ∉ ker f`, some `u ∈ f` misses `x`; then
  `t = s ∪ u ∈ f` contains `s` but misses `x`, so it is not `univ`.
  Hence the condition forces `(ker f)ᶜ ⊆ s`.
- Conversely if `(ker f)ᶜ ⊆ s` and `s ⊆ t ∈ f`, then `t` contains
  `ker f` and `(ker f)ᶜ`, so `t = univ`.

Examples: `￢(𝓟 t) = 𝓟 tᶜ` (since `ker (𝓟 t) = t`, see
`principal_has_set_kernel` above), e.g. `￢(pure 0) = 𝓟 {n | n ≠ 0}`.
The cofinite filter on `ℕ` has empty kernel, so its negation is
`𝓟 univ = ⊤`. -/
instance instHNot : HNot (Filter α) where
  hnot f := 𝓟 f.kerᶜ

/-- Unfolds the definition of `f \ g`; `Iff.rfl` since it is
literally the definition. -/
theorem mem_sdiff : s ∈ f \ g ↔ ∀ t ∈ g, s ⊆ t → t ∈ f := .rfl

/-- Unfolds the definition of `￢f`, again by `rfl`. -/
protected theorem hnot_def : ￢f = 𝓟 f.kerᶜ := rfl


/-- A filter is `NeBot` if it is not equal to `⊥`, or equivalently the empty set does not belong to
the filter. Bourbaki include this assumption in the definition of a filter but we prefer to have a
`CompleteLattice` structure on `Filter _`, so we use a typeclass argument in lemmas instead.

Why `f ≠ ⊥ ↔ ∅ ∉ f`: if `∅ ∈ f`, every set is a superset of `∅`,
so `f` contains every set and `f = ⊥`; conversely `∅ ∈ ⊥`.

Examples: `pure a`, the cofinite filter on `ℕ`, `atTop` and every
ultrafilter are `NeBot`; `𝓟 ∅ = ⊥` is not.

`class` (instead of `structure`) means Lean finds the proof by
itself: a lemma stated with `[NeBot f]` gets this hypothesis
automatically whenever an instance for `f` is known (for example
Mathlib declares `atTop` on `ℕ` to be `NeBot` once and for all).

On paper this is the usual assumption "`f` is a proper filter". -/
class NeBot (f : Filter α) : Prop where
  /-- The filter is nontrivial: `f ≠ ⊥` or equivalently, `∅ ∉ f`. -/
  ne' : f ≠ ⊥

/-- Passing between the class and the plain statement `f ≠ ⊥`.
`h.1` extracts the field `ne'`; `⟨h⟩` builds the class from it.
The tag `@[push ←]` registers the lemma with Mathlib's `push`
tactics (used e.g. when pushing negations), read right to left,
so that `f ≠ ⊥` is rewritten as `NeBot f`. -/
@[push ←]
theorem neBot_iff {f : Filter α} : NeBot f ↔ f ≠ ⊥ :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩

/-- `f.Eventually p` or `∀ᶠ x in f, p x` mean that `{x | p x} ∈ f`. E.g., `∀ᶠ x in atTop, p x`
means that `p` holds true for sufficiently large `x`.

This is the central notion: "`p x` holds for `f`-almost all `x`".
Examples, with `p : α → Prop`:
- `∀ᶠ x in pure a, p x ↔ p a`;
- `∀ᶠ x in ⊤, p x ↔ ∀ x, p x`;
- `∀ᶠ x in 𝓟 s, p x ↔ ∀ x ∈ s, p x`;
- `∀ᶠ n in cofinite, p n`: `p` fails only at finitely many `n`,
  e.g. `∀ᶠ n in cofinite, n ≥ 10` holds on `ℕ`;
- `∀ᶠ x in ⊥, p x` holds for every `p`, even `False`;
- for an ultrafilter `U`: `p` holds on a `U`-large set, the
  condition in Łoś's theorem (see `Los.lean`).

The filter axioms become logic rules:
`univ_mem` gives `∀ᶠ x in f, True`, `mem_of_superset` lets us
weaken `p` to any `q` with `p → q`, and `inter_mem` combines
`∀ᶠ x, p x` and `∀ᶠ x, q x` into `∀ᶠ x, p x ∧ q x`. -/
protected def Eventually (p : α → Prop) (f : Filter α) : Prop :=
  { x | p x } ∈ f

@[inherit_doc Filter.Eventually]
notation3 "∀ᶠ "(...)" in "f", "r:(scoped p => Filter.Eventually p f) => r

/-- `f.Frequently p` or `∃ᶠ x in f, p x` mean that `{x | ¬p x} ∉ f`. E.g., `∃ᶠ x in atTop, p x`
means that there exist arbitrarily large `x` for which `p` holds true.

Definition: `∃ᶠ x in f, p x` is `¬ ∀ᶠ x in f, ¬ p x`, the same
duality as `∃ = ¬∀¬`. Equivalently, `{x | p x}` meets every set
of `f`.

Example on `ℕ` with the cofinite filter: `∃ᶠ n, Even n` holds
(the odd numbers are not cofinite), but `∀ᶠ n, Even n` fails.

Relations with `Eventually`:
- if `f` is `NeBot`, then `∀ᶠ` implies `∃ᶠ`;
- along `⊥`, `∃ᶠ` is always false (since `∀ᶠ` is always true);
- along an ultrafilter, `∃ᶠ` and `∀ᶠ` coincide: exactly one of
  `{x | p x}` and its complement belongs to the ultrafilter. -/
protected def Frequently (p : α → Prop) (f : Filter α) : Prop :=
  ¬∀ᶠ x in f, ¬p x

@[inherit_doc Filter.Frequently]
notation3 "∃ᶠ "(...)" in "f", "r:(scoped p => Filter.Frequently p f) => r

/-- Two functions `f` and `g` are *eventually equal* along a filter `l` if the set of `x` such that
`f x = g x` belongs to `l`.

Examples: `f =ᶠ[cofinite] g` means `f` and `g` differ at finitely
many points; `f =ᶠ[pure a] g` means `f a = g a`.
For an ultrafilter `U`, this is exactly when the classes of `f`
and `g` in the ultrapower are equal (`Ultra.ofFun_eq_ofFun` in
`Basic.lean`). -/
def EventuallyEq (l : Filter α) (f g : α → β) : Prop :=
  ∀ᶠ x in l, f x = g x

/-- A function `f` is eventually less than or equal to a function `g` at a filter `l`.

Example: `(fun n ↦ n) ≤ᶠ[cofinite] (fun n ↦ n ^ 2 - 5)` on `ℕ`,
since `n ≤ n ^ 2 - 5` fails only for `n = 1, 2`
(on `ℕ`, `1 - 5 = 0`).

The tag `@[to_dual self (reorder := f g)]` tells Mathlib that the
order-dual of this definition is itself with `f` and `g` swapped:
reversing the order turns `f ≤ g` into `g ≤ f`. -/
@[to_dual self (reorder := f g)]
def EventuallyLE [LE β] (l : Filter α) (f g : α → β) : Prop :=
  ∀ᶠ x in l, f x ≤ g x

/-- Two sets `s` and `t` are *eventually equal* along a filter `l` if the set of `x` such that
`x ∈ s ↔ x ∈ t` belongs to `l`.

This is `EventuallyEq` for the indicator functions of `s` and `t`.
Example: `s =ᶠ[cofinite] t` iff the symmetric difference of `s`
and `t` is finite. -/
def EventuallyEqSet (l : Filter α) (s t : Set α) : Prop :=
  ∀ᶠ x in l, x ∈ s ↔ x ∈ t

/-- A set `s` is *eventually contained* in a set `t` along a filter `l` if the set of `x` such that
`x ∈ s → x ∈ t` belongs to `l`.

Example: `s ≤ᶠ[cofinite] t` iff `s \ t` is finite. -/
def EventuallySubset (l : Filter α) (s t : Set α) : Prop :=
  ∀ᶠ x in l, x ∈ s → x ∈ t

/-!
### Notation machinery for `=ᶠ[l]` and `≤ᶠ[l]` (no mathematics here)

The next declarations only make the notation work; they can be
skipped when studying filters.
- `syntax` declares how `x =ᶠ[l] y` and `x ≤ᶠ[l] y` are written.
- `elabEventuallyRelSides`, `elabEventuallyEq`, `elabEventuallyLE`
  look at the type of `x` (or of `y` if `x`'s type is unknown) and
  translate the notation into `EventuallyEqSet` / `EventuallySubset`
  when it is a `Set`, and into `EventuallyEq` / `EventuallyLE`
  when it is a function.
- `precheck...` lets the notation appear inside other notations.
- `unexpand...` makes Lean print the definitions back with the
  short notation, e.g. `EventuallyEq l f g` is shown as `f =ᶠ[l] g`.
`meta def` marks code that runs while Lean reads the file, not
mathematical definitions.
-/

/-- `x =ᶠ[l] y` means that `x` and `y` are *eventually equal* along the filter `l`.

This is `Filter.EventuallyEq l x y` if `x` is a function or `Filter.EventuallyEqSet l x y` if `x`
is a set. -/
syntax:50 (name := eventuallyEqStx) term:51 " =ᶠ[" term "] " term:50 : term

/-- `x ≤ᶠ[l] y` means that `x` is *eventually less than or equal to* `y` along the filter `l`.

This is `Filter.EventuallyLE l x y` if `x` is a function and `Filter.EventuallySubset l x y` if `x`
is a set. -/
syntax:50 (name := eventuallyLEStx) term:51 " ≤ᶠ[" term "] " term:50 : term

open Lean Elab Term Meta in
/-- Elaborate the left-hand side `x` of an `x =ᶠ[l] y` / `x ≤ᶠ[l] y` on its own, dispatching on
whether its type is a `Set`. If the type is not yet known (e.g. `x` is the `_` of a `calc` step),
consult the right-hand side `y` instead. Returns the elaborated sides turned back into syntax
together with whether they should be interpreted as sets. If `y` is not consulted, it is returned
unelaborated. -/
meta def elabEventuallyRelSides (x y : Term) : TermElabM (Term × Term × Bool) := do
  -- Elaborate a side on its own, and return its type in whnf together with the elaborated term
  -- turned back into syntax.
  let elabSide (e : Term) : TermElabM (Expr × Term) := do
    let e ← elabTerm e none
    return (← whnfR (← instantiateMVars (← inferType e)), ← exprToSyntax e)
  let (tyx, x) ← elabSide x
  if tyx.getAppFn.isMVar then
    let (tyy, y) ← elabSide y
    return (x, y, tyy.isAppOfArity ``Set 1)
  else
    return (x, y, tyx.isAppOfArity ``Set 1)

open Lean Elab Term in
/-- Elaborator for `x =ᶠ[l] y`, dispatching on the type of `x` (or of `y` if the type of `x` is not
yet known): `Filter.EventuallyEqSet` for sets, `Filter.EventuallyEq` for functions. -/
@[term_elab eventuallyEqStx]
meta def elabEventuallyEq : TermElab := fun stx expectedType? => do
  let `($x =ᶠ[$l] $y) := stx | throwUnsupportedSyntax
  let (x, y, isSet) ← elabEventuallyRelSides x y
  if isSet then
    elabTerm (← `(Filter.EventuallyEqSet $l $x $y)) expectedType?
  else
    elabTerm (← `(Filter.EventuallyEq $l $x $y)) expectedType?

open Lean Elab Term in
/-- Elaborator for `x ≤ᶠ[l] y`, dispatching on the type of `x` (or of `y` if the type of `x` is not
yet known): `Filter.EventuallySubset` for sets, `Filter.EventuallyLE` for functions. -/
@[term_elab eventuallyLEStx]
meta def elabEventuallyLE : TermElab := fun stx expectedType? => do
  let `($x ≤ᶠ[$l] $y) := stx | throwUnsupportedSyntax
  let (x, y, isSet) ← elabEventuallyRelSides x y
  if isSet then
    elabTerm (← `(Filter.EventuallySubset $l $x $y)) expectedType?
  else
    elabTerm (← `(Filter.EventuallyLE $l $x $y)) expectedType?

open Lean.Elab Term.Quotation in
/-- `quot_precheck` for the `=ᶠ[l]` notation, allowing it to appear inside other notations. -/
@[quot_precheck Filter.eventuallyEqStx] meta def precheckEventuallyEq : Precheck
  | `($x =ᶠ[$l] $y) => do precheck x; precheck l; precheck y
  | _ => throwUnsupportedSyntax

open Lean.Elab Term.Quotation in
/-- `quot_precheck` for the `≤ᶠ[l]` notation, allowing it to appear inside other notations. -/
@[quot_precheck Filter.eventuallyLEStx] meta def precheckEventuallyLE : Precheck
  | `($x ≤ᶠ[$l] $y) => do precheck x; precheck l; precheck y
  | _ => throwUnsupportedSyntax

/-- Unexpander printing `Filter.EventuallyEq l f g` as `f =ᶠ[l] g`. -/
@[app_unexpander Filter.EventuallyEq]
meta def unexpandEventuallyEq : Lean.PrettyPrinter.Unexpander
  | `($_ $l $f $g) => `($f =ᶠ[$l] $g)
  | _ => throw ()

/-- Unexpander printing `Filter.EventuallyEqSet l s t` as `s =ᶠ[l] t`. -/
@[app_unexpander Filter.EventuallyEqSet]
meta def unexpandEventuallyEqSet : Lean.PrettyPrinter.Unexpander
  | `($_ $l $s $t) => `($s =ᶠ[$l] $t)
  | _ => throw ()

/-- Unexpander printing `Filter.EventuallyLE l f g` as `f ≤ᶠ[l] g`. -/
@[app_unexpander Filter.EventuallyLE]
meta def unexpandEventuallyLE : Lean.PrettyPrinter.Unexpander
  | `($_ $l $f $g) => `($f ≤ᶠ[$l] $g)
  | _ => throw ()

/-- Unexpander printing `Filter.EventuallySubset l s t` as `s ≤ᶠ[l] t`. -/
@[app_unexpander Filter.EventuallySubset]
meta def unexpandEventuallySubset : Lean.PrettyPrinter.Unexpander
  | `($_ $l $s $t) => `($s ≤ᶠ[$l] $t)
  | _ => throw ()

/-- The forward map of a filter

`s ∈ map m f ↔ m ⁻¹' s ∈ f`: a set is large for the image filter
when its preimage is large for `f`. This is the analogue of the
push-forward of a measure, `μ ∘ m⁻¹`.

On paper: `map m f` is the filter generated by the images `m(a)`,
`a ∈ f`. Indeed `m(a) ⊆ s` gives `a ⊆ m⁻¹(s)`, and conversely
`m(m⁻¹(s)) ⊆ s`. We cannot take the images themselves, since
they are not closed under supersets.

Examples:
- `map m (pure a) = pure (m a)`;
- `map m (𝓟 s) = 𝓟 (m '' s)`;
- `map (fun n ↦ 2 * n) atTop` on `ℕ`: `s` is in it iff `s`
  contains all large even numbers;
- for an ultrafilter `U` on `ℕ`, `map (· % 2) U` is `pure 0` or
  `pure 1`, depending on whether the evens are in `U`.

The axioms are those of `f`, since preimage commutes with
everything: `m ⁻¹' univ = univ`, preimage is monotone, and
`m ⁻¹' (s ∩ t) = m ⁻¹' s ∩ m ⁻¹' t` (all by definition, so the
proofs are just `univ_mem`, `mem_of_superset`, `inter_mem`).
Note `preimage m ⁻¹' f.sets` is a preimage of a preimage: the
family of sets `s` whose preimage `m ⁻¹' s` lies in `f.sets`. -/
def map (m : α → β) (f : Filter α) : Filter β where
  sets := preimage m ⁻¹' f.sets
  univ_sets := univ_mem
  sets_of_superset hs st := mem_of_superset hs fun _x hx ↦ st hx
  inter_sets hs ht := inter_mem hs ht

/-- `Filter.Tendsto` is the generic "limit of a function" predicate.
  `Tendsto f l₁ l₂` asserts that for every `l₂` neighborhood `a`,
  the `f`-preimage of `a` is an `l₁` neighborhood.

Unfolding: `map f l₁ ≤ l₂` means every set of `l₂` is in
`map f l₁`, i.e. `∀ s ∈ l₂, f ⁻¹' s ∈ l₁`, or
`∀ s ∈ l₂, ∀ᶠ x in l₁, f x ∈ s`.

One definition covers all the limits of analysis:
- `Tendsto a atTop (𝓝 L)`: the sequence `a n → L`
  (for every neighbourhood `U` of `L`, eventually `a n ∈ U`);
- `Tendsto f (𝓝 x) (𝓝 (f x))`: `f` is continuous at `x`;
- `Tendsto f atTop atTop`: `f x → ∞` as `x → ∞`.
Here `𝓝 x` is the neighbourhood filter, defined in topology.

Composition is immediate: if `Tendsto f l₁ l₂` and
`Tendsto g l₂ l₃`, then `Tendsto (g ∘ f) l₁ l₃`. -/
def Tendsto (f : α → β) (l₁ : Filter α) (l₂ : Filter β) :=
  l₁.map f ≤ l₂

/-- The inverse map of a filter. A set `s` belongs to `Filter.comap m f` if either of the following
equivalent conditions hold.

1. There exists a set `t ∈ f` such that `m ⁻¹' t ⊆ s`. This is used as a definition.
2. The set `kernImage m s = {y | ∀ x, m x = y → x ∈ s}` belongs to `f`, see `Filter.mem_comap'`.
3. The set `(m '' sᶜ)ᶜ` belongs to `f`, see `Filter.mem_comap_iff_compl` and
   `Filter.compl_mem_comap`.

Pulling a filter back along `m : α → β`. The preimages `m ⁻¹' t`
(`t ∈ f`) are closed under intersections but not under supersets,
so we take every set containing one of them: hence `⊆` and not `=`
in the definition (the same idea as in `⊓`, done here with `⊆`).

The axioms:
- `univ`: `m ⁻¹' univ ⊆ univ`, with `univ ∈ f`.
- Superset: `m ⁻¹' a' ⊆ a ⊆ b`, by transitivity.
- Intersection: use `a' ∩ b' ∈ f`, whose preimage is contained in
  the intersection of the two sets (`inter_subset_inter`).

Examples:
- `comap m (𝓟 t) = 𝓟 (m ⁻¹' t)`;
- with the inclusion `ℕ → ℤ`, `comap` of `atTop` on `ℤ` is
  `atTop` on `ℕ`;
- `comap` can give `⊥`: if `m` is constant `0` and `f = pure 1`,
  then `m ⁻¹' {1} = ∅` belongs to `comap m f`.

`map` and `comap` are adjoint: `map m g ≤ f ↔ g ≤ comap m f`
(Mathlib: `map_le_iff_le_comap`), i.e.
`Tendsto m g f ↔ g ≤ comap m f`.
-/
def comap (m : α → β) (f : Filter β) : Filter α where
  sets := { s | ∃ t ∈ f, m ⁻¹' t ⊆ s }
  univ_sets := ⟨univ, univ_mem, subset_univ _⟩
  sets_of_superset := fun ⟨a', ha', ma'a⟩ ab => ⟨a', ha', ma'a.trans ab⟩
  inter_sets := fun ⟨a', ha₁, ha₂⟩ ⟨b', hb₁, hb₂⟩ =>
    ⟨a' ∩ b', inter_mem ha₁ hb₁, inter_subset_inter ha₂ hb₂⟩

/-- Coproduct of filters.

`comap Prod.fst f` contains the sets containing a strip `a × β`
with `a ∈ f`; `comap Prod.snd g` those containing `α × b`, `b ∈ g`.
Their `⊔` (sets in both) contains the sets containing a "cross"
`(a × β) ∪ (α × b)`.

Example: `(pure x).coprod (pure y)` is generated by the cross
`({x} × β) ∪ (α × {y})` through the point `(x, y)`. Compare with
the product below, which gives the single point. -/
protected def coprod (f : Filter α) (g : Filter β) : Filter (α × β) :=
  f.comap Prod.fst ⊔ g.comap Prod.snd

/-- Product of filters. This is the filter generated by Cartesian products
of elements of the component filters.

`f ×ˢ g = comap Prod.fst f ⊓ comap Prod.snd g`. Since
`(a × β) ∩ (α × b) = a × b`, by the description of `⊓`:
`s ∈ f ×ˢ g ↔ ∃ a ∈ f, ∃ b ∈ g, a ×ˢ b ⊆ s` (rectangles).

Examples:
- `pure x ×ˢ pure y = pure (x, y)`;
- `atTop ×ˢ atTop` on `ℕ × ℕ`: "both coordinates large".

Warning: for ultrafilters `U`, `V`, `U ×ˢ V` is in general not an
ultrafilter. For a non-principal `U` on `ℕ`, the set
`{(m, n) | m < n}` contains no infinite rectangle and neither does
its complement. The iterated construction `curry` below decides
such sets; it is the tensor product of ultrafilters. -/
instance instSProd : SProd (Filter α) (Filter β) (Filter (α × β)) where
  sprod f g := f.comap Prod.fst ⊓ g.comap Prod.snd

/-- The definition, as a theorem to rewrite with; `rfl`. -/
theorem prod_eq_inf (f : Filter α) (g : Filter β) : f ×ˢ g = f.comap Prod.fst ⊓ g.comap Prod.snd :=
  rfl

/-- The product of an indexed family of filters.

`⨅ i, comap (Function.eval i) (f i)`, where `Function.eval i x = x i`.
`comap (eval i) (f i)` is generated by the sets `{x | x i ∈ a}`,
`a ∈ f i` (a condition on coordinate `i` only). The infimum is
generated by finite intersections of these, so the sets of `pi f`
are those containing a *cylinder*: finitely many coordinates
restricted to large sets, the others free. This is like the
product topology.

It is the analogue of `f ×ˢ g` for any number of factors. -/
def pi {ι : Type*} {α : ι → Type*} (f : ∀ i, Filter (α i)) : Filter (∀ i, α i) :=
  ⨅ i, comap (Function.eval i) (f i)

/-- The monadic bind operation on filter is defined the usual way in terms of `map` and `join`.

Unfortunately, this `bind` does not result in the expected applicative. See `Filter.seq` for the
applicative instance.

Unfolding `join` and `map`:
`s ∈ bind f m ↔ {a | s ∈ m a} ∈ f`,
i.e. `s` belongs to `m a` for `f`-almost every `a`.
Think of `m` as a family of filters indexed by `α`, averaged
along `f`.

Examples:
- `bind (pure a) m = m a`;
- `bind f pure = f`;
- `bind f (fun _ ↦ g) = g` when `f` is `NeBot` (for `f = ⊥` the
  result is `⊥`, since then `∅ ∈ f`). -/
def bind (f : Filter α) (m : α → Filter β) : Filter β :=
  join (map m f)

/-- The applicative sequentiation operation. This is not induced by the bind operation.

`f` is a filter on functions `α → β`, `g` a filter on `α`.
`s ∈ seq f g` iff there are `u ∈ f` and `t ∈ g` with `m x ∈ s` for
all `m ∈ u` and `x ∈ t`: `s` contains "the functions of `u`
applied to the points of `t`". This is a rectangle condition,
like `×ˢ`.

The version induced by `bind` would instead be
`{m | {x | m x ∈ s} ∈ g} ∈ f`, an iterated condition like `curry`.
That is the difference the docstring of `bind` refers to.

Example: `seq (pure m) g = map m g`.

The axioms: `univ` with `u = t = univ`; superset by composing with
`s ⊆ s'`; intersection by intersecting both `u`'s and both `t`'s. -/
def seq (f : Filter (α → β)) (g : Filter α) : Filter β where
  sets := { s | ∃ u ∈ f, ∃ t ∈ g, ∀ m ∈ u, ∀ x ∈ t, (m : α → β) x ∈ s }
  univ_sets := ⟨univ, univ_mem, univ, univ_mem, fun _ _ _ _ => trivial⟩
  sets_of_superset := fun ⟨t₀, t₁, h₀, h₁, h⟩ hst =>
    ⟨t₀, t₁, h₀, h₁, fun _ hx _ hy => hst <| h _ hx _ hy⟩
  inter_sets := fun ⟨t₀, ht₀, t₁, ht₁, ht⟩ ⟨u₀, hu₀, u₁, hu₁, hu⟩ =>
    ⟨t₀ ∩ u₀, inter_mem ht₀ hu₀, t₁ ∩ u₁, inter_mem ht₁ hu₁, fun _ ⟨hx₀, hx₁⟩ _ ⟨hy₀, hy₁⟩ =>
      ⟨ht _ hx₀ _ hy₀, hu _ hx₁ _ hy₁⟩⟩

/-- This filter is characterized by `Filter.eventually_curry_iff`:
`(∀ᶠ (x : α × β) in f.curry g, p x) ↔ ∀ᶠ (x : α) in f, ∀ᶠ (y : β) in g, p (x, y)`. Useful
in adding quantifiers to the middle of `Tendsto`s. See
`hasFDerivAt_of_tendstoUniformlyOnFilter`.

From the description of `bind`:
`s ∈ f.curry g ↔ {a | {b | (a, b) ∈ s} ∈ g} ∈ f`.
For ultrafilters this is the tensor product `U ⊗ V` (compare with
`Tensor.lean`), and it is again an ultrafilter.

`curry` is finer than the product: `f.curry g ≤ f ×ˢ g`. If
`a ×ˢ b ⊆ s`, then for each `x ∈ a` the slice `{y | (x, y) ∈ s}`
contains `b ∈ g`, so the set of such `x` contains `a ∈ f`.

Example where they differ, on `ℕ × ℕ` with `atTop`:
`S = {(m, n) | m < n}` is in `atTop.curry atTop` (for each `m`,
eventually `n > m`), but not in `atTop ×ˢ atTop` (a rectangle
`a ×ˢ b` with `a` unbounded has points with `m` larger than
some `n ∈ b`). The order of the two variables matters here. -/
def curry (f : Filter α) (g : Filter β) : Filter (α × β) :=
  bind f fun a ↦ map (a, ·) g

/-- These two instances register `bind` and `map` with Lean's
general notations: `f >>= m` for `bind f m`, and `m <$> f` for
`map m f`. No mathematics is added. -/
instance : Bind Filter :=
  ⟨@Filter.bind⟩

instance : Functor Filter where map := @Filter.map

/-- A variant on `bind` using a function `g` taking a set instead of a member of `α`.
This is essentially a push-forward along a function mapping each set to a filter.

`f.lift g = ⨅ s ∈ f, g s`: the infimum (generated by the union) of
the filters `g s`, over the sets `s` of `f`.
When `g` is monotone (`s ⊆ s'` gives `g s ≤ g s'`), this simplifies
to `t ∈ f.lift g ↔ ∃ s ∈ f, t ∈ g s` (Mathlib: `mem_lift_sets`).

Example: `f.lift 𝓟 = f`, since `t ∈ 𝓟 s` means `s ⊆ t`. -/
protected def lift (f : Filter α) (g : Set α → Filter β) :=
  ⨅ s ∈ f, g s

/-- Specialize `lift` to functions `Set α → Set β`. This can be viewed as a generalization of `map`.
This is essentially a push-forward along a function mapping each set to a set.

`f.lift' h` is generated by the sets `h s`, `s ∈ f`. When `h` is
monotone: `t ∈ f.lift' h ↔ ∃ s ∈ f, h s ⊆ t`.

Examples:
- `h s = m '' s` gives `map m f` (see the note on `map`);
- `h = id` gives `f`;
- `h s = s ×ˢ s` gives the filter of "pairs both in a small set",
  used for Cauchy filters in uniform spaces;
- `h = closure` gives the filter generated by closures. -/
protected def lift' (f : Filter α) (h : Set α → Set β) :=
  f.lift (𝓟 ∘ h)

/-- `f.IsBounded r`: the filter `f` is eventually bounded w.r.t. the relation `r`,
i.e. eventually, it is bounded by some uniform bound.
`r` will be usually instantiated with `(· ≤ ·)` or `(· ≥ ·)`.

With `r = (· ≤ ·)`: there is `b` with `x ≤ b` for `f`-almost all
`x`, i.e. `f` is eventually bounded above.
Examples on `ℝ`: `𝓟 [0, 1]` is bounded; `atTop` is not.
Note `b` must be uniform: one bound for almost all `x`. -/
def IsBounded (r : α → α → Prop) (f : Filter α) :=
  ∃ b, ∀ᶠ x in f, r x b

/-- `f.IsBoundedUnder (≺) u`: the image of the filter `f` under `u` is eventually bounded w.r.t.
the relation `≺`, i.e. eventually, it is bounded by some uniform bound.

Unfolding `map`: `∃ b, ∀ᶠ x in f, r (u x) b`.
Example: for the sequence `u n = (-1) ^ n` and `f = atTop`, it is
bounded under `≤` (take `b = 1`); `u n = n` is not.
This is the hypothesis needed to talk about `limsup u`. -/
def IsBoundedUnder (r : α → α → Prop) (f : Filter β) (u : β → α) :=
  (map u f).IsBounded r

/-- `IsCobounded (≺) f` states that the filter `f` does not tend to infinity w.r.t. `≺`. This is
also called frequently bounded. Will be usually instantiated with `≤` or `≥`.

There is a subtlety in this definition: we want `f.IsCobounded` to hold for any `f` in the case of
complete lattices. This will be relevant to deduce theorems on complete lattices from their
versions on conditionally complete lattices with additional assumptions. We have to be careful in
the edge case of the trivial filter containing the empty set: the other natural definition
  `¬ ∀ a, ∀ᶠ n in f, a ≤ n`
would not work as well in this case.

With `r = (· ≤ ·)`: call `a` an *eventual upper bound* if
`∀ᶠ x in f, x ≤ a`. The definition asks for `b` below every
eventual upper bound, i.e. the eventual upper bounds are bounded
below. It fails when every `a` is an eventual upper bound, which
is when `f` escapes to `-∞`.

Examples (as `IsCoboundedUnder (· ≤ ·) atTop u` on `ℝ`):
- `u n = -n`: every `a` is an eventual upper bound, so it fails;
- `u n = n`: no eventual upper bound at all, so any `b` works;
- `u n = (-1) ^ n`: the eventual upper bounds are `a ≥ 1`, take
  `b = 1` (or anything `≤ 1`).

Why it matters: `limsup` is the infimum of the eventual upper
bounds. That set must be nonempty (`IsBounded`) and bounded below
(`IsCobounded`) for the infimum to make sense in `ℝ`.

The edge case `f = ⊥`: every `a` is an eventual upper bound. In a
complete lattice `b = ⊥` still works, so `IsCobounded` holds,
whereas the alternative `¬ ∀ a, ∀ᶠ n in f, a ≤ n` would be false.
-/
def IsCobounded (r : α → α → Prop) (f : Filter α) :=
  ∃ b, ∀ a, (∀ᶠ x in f, r x a) → r b a

/-- `IsCoboundedUnder (≺) f u` states that the image of the filter `f` under the map `u` does not
tend to infinity w.r.t. `≺`. This is also called frequently bounded. Will be usually instantiated
with `≤` or `≥`.

Unfolding `map`: `∃ b, ∀ a, (∀ᶠ x in f, r (u x) a) → r b a`. -/
def IsCoboundedUnder (r : α → α → Prop) (f : Filter β) (u : β → α) :=
  (map u f).IsCobounded r

end Filter

namespace Mathlib.Tactic

open Lean Meta Elab Tactic

/--
`filter_upwards [h₁, ⋯, hₙ]` replaces a goal of the form `s ∈ f` and terms
`h₁ : t₁ ∈ f, ⋯, hₙ : tₙ ∈ f` with `∀ x, x ∈ t₁ → ⋯ → x ∈ tₙ → x ∈ s`.
The list is an optional parameter, `[]` being its default value.

`filter_upwards [h₁, ⋯, hₙ] with a₁ a₂ ⋯ aₖ` is a short form for
`{ filter_upwards [h₁, ⋯, hₙ], intro a₁ a₂ ⋯ aₖ }`.

`filter_upwards [h₁, ⋯, hₙ] using e` is a short form for
`{ filter_upwards [h1, ⋯, hn], exact e }`.

Combining both shortcuts is done by writing `filter_upwards [h₁, ⋯, hₙ] with a₁ a₂ ⋯ aₖ using e`.
Note that in this case, the `aᵢ` terms can be used in `e`.

Example: with `h₁ : t₁ ∈ f`, `h₂ : t₂ ∈ f` and goal `s ∈ f`,
`filter_upwards [h₁, h₂] with x hx₁ hx₂` leaves the goal `x ∈ s`
with `hx₁ : x ∈ t₁` and `hx₂ : x ∈ t₂`.
Why this is valid: `t₁ ∩ t₂ ∈ f` (`inter_mem`) and a superset of a
set of `f` is in `f` (`mem_of_superset`); so it suffices to show
`t₁ ∩ t₂ ⊆ s`, pointwise.
It works the same for `∀ᶠ` goals, since `∀ᶠ x in f, p x` is
`{x | p x} ∈ f`.

How the code below does it: for each `hᵢ`, from the last to the
first, it applies `Filter.mp_mem` (modus ponens for filters,
`t ∈ f → {x | x ∈ t → x ∈ s} ∈ f → s ∈ f`), which moves the
hypothesis into the goal. Then `Filter.univ_mem'` turns
"`... ∈ f` for a set true everywhere" into `∀ x, ...`. Finally
`dsimp` tidies, `intro` names the variables (`with`), and
`exact` closes the goal (`using`).
-/
syntax (name := filterUpwards) "filter_upwards" (" [" term,* "]")?
  (" with" (ppSpace colGt term:max)*)? (" using " term)? : tactic

elab_rules : tactic
| `(tactic| filter_upwards $[[$[$args],*]]? $[with $wth*]? $[using $usingArg]?) => do
  focus do
    let config : ApplyConfig := {newGoals := ApplyNewGoals.nonDependentOnly}
    for e in args.getD #[] |>.reverse do
      let goal ← getMainGoal
      replaceMainGoal <| ← goal.withContext <| runTermElab do
        let m ← mkFreshExprMVar none
        let lem ← Term.elabTermEnsuringType
          (← ``(Filter.mp_mem $e $(← Term.exprToSyntax m))) (← goal.getType)
        goal.assign lem
        return [m.mvarId!]
    liftMetaTactic fun goal => do
      goal.apply (← mkConstWithFreshMVarLevels ``Filter.univ_mem') config
    evalTactic <|← `(tactic| try dsimp -zeta only [Set.mem_ofPred_eq])
    if let some l := wth then
      evalTactic <|← `(tactic| intro $[$l]*)
    if let some e := usingArg then
      evalTactic <|← `(tactic| exact $e)

end Mathlib.Tactic
